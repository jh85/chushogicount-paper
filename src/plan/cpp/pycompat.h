// Licensing/provenance: CPython tuple/set/random compatibility adapted to C++
// square-index keys, fixed-width state and 32-bit seeds, without Python runtime
// interfaces. Original project additions are Apache-2.0. CPython-derived portions
// retain the PSF License Version 2 reproduced in ../../../THIRD_PARTY.md.
// Copyright (c) 2001 Python Software Foundation; All Rights Reserved.
// The MT19937 implementation retains its original notice below.
/*
Copyright (C) 1997 - 2002, Makoto Matsumoto and Takuji Nishimura,
All rights reserved.

Redistribution and use in source and binary forms, with or without
modification, are permitted provided that the following conditions
are met:

  1. Redistributions of source code must retain the above copyright
 notice, this list of conditions and the following disclaimer.

  2. Redistributions in binary form must reproduce the above copyright
 notice, this list of conditions and the following disclaimer in the
 documentation and/or other materials provided with the distribution.

  3. The names of its contributors may not be used to endorse or promote
 products derived from this software without specific prior written
 permission.

THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
"AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
A PARTICULAR PURPOSE ARE DISCLAIMED.  IN NO EVENT SHALL THE COPYRIGHT OWNER OR
CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL,
EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO,
PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR
PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF
LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING
NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS
SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
*/
// Bit-exact emulation of the CPython 3.14 behaviour the Python planner depends on:
//  * PySquareSet: iteration order of a CPython `set` of (x, r) tuples (frontier regions,
//    the peel strategy's `inserted` set);
//  * PyRandom: random.Random(seed) (MT19937, init_by_array) and Random.shuffle.
// Checked against the interpreter by tests/test_cplanner.py (pycompat section).
#pragma once
#include <cstdint>
#include <vector>

namespace cp {

// hash((x, r)) for small ints (tuple xxHash variant, Objects/tupleobject.c)
inline uint64_t tuple2_hash(int64_t a, int64_t b) {
  const uint64_t P1 = 11400714785074694791ULL, P2 = 14029467366897019727ULL,
                 P5 = 2870177450012600261ULL;
  auto ih = [](int64_t v) -> uint64_t { return v == -1 ? (uint64_t)-2 : (uint64_t)v; };
  uint64_t acc = P5;
  for (uint64_t lane : {ih(a), ih(b)}) {
    acc += lane * P2;
    acc = (acc << 31) | (acc >> 33);
    acc *= P1;
  }
  acc += 2 ^ (P5 ^ 3527539ULL);
  if (acc == (uint64_t)-1) return 1546275796ULL;
  return acc;
}

// Objects/setobject.c: open addressing, LINEAR_PROBES 9, PERTURB_SHIFT 5, dummies on
// discard, resize when fill*5 >= mask*3.  Keys are square indices 0..143 (x*12 + r-1).
class PySquareSet {
 public:
  PySquareSet() { reset(8); }
  bool contains(int sq) const {
    if (!has_[sq]) return false;
    return true;
  }
  size_t size() const { return used_; }
  void add(int sq) {
    if (has_[sq]) return;
    uint64_t h = hash_of(sq);
    size_t mask = table_.size() - 1;
    size_t i = h & mask;
    uint64_t perturb = h;
    long freeslot = -1;               // a dummy on the probe sequence is reused
    while (true) {
      size_t probes = (i + 9 <= mask) ? 9 : 0;
      size_t j = i;
      while (true) {
        if (table_[j] == EMPTY) {
          if (freeslot >= 0) {
            table_[freeslot] = sq;
            has_[sq] = true;
            ++used_;
            return;
          }
          place(j, sq);
          return;
        }
        if (table_[j] == DUMMY) freeslot = (long)j;   // the last dummy seen (checked empirically)
        if (probes-- == 0) break;
        ++j;
      }
      perturb >>= 5;
      i = (i * 5 + 1 + perturb) & mask;
    }
  }
  void discard(int sq) {
    if (!has_[sq]) return;
    for (auto& e : table_)
      if (e == sq) { e = DUMMY; break; }
    has_[sq] = false;
    --used_;
  }
  // set(other): Objects/setobject.c set_merge into an empty set
  static PySquareSet copy_of(const PySquareSet& o) {
    PySquareSet s;
    if (o.used_ == 0) return s;
    if ((0 + o.used_) * 5 >= (s.table_.size() - 1) * 3) s.resize((0 + o.used_) * 2);
    if (s.table_.size() == o.table_.size() && o.fill_ == o.used_) {
      s.table_ = o.table_;
      s.fill_ = o.fill_;
      s.used_ = o.used_;
      s.has_ = o.has_;
      return s;
    }
    for (int k : o.table_)
      if (k >= 0) s.insert_clean(k);
    s.fill_ = s.used_ = o.used_;
    for (int k : o.table_)
      if (k >= 0) s.has_[k] = true;
    return s;
  }
  std::vector<int> items() const {
    std::vector<int> out;
    for (int k : table_)
      if (k >= 0) out.push_back(k);
    return out;
  }

 private:
  static constexpr int EMPTY = -1, DUMMY = -2;
  std::vector<int> table_;
  size_t fill_ = 0, used_ = 0;
  std::vector<bool> has_ = std::vector<bool>(144, false);

  static uint64_t hash_of(int sq) { return tuple2_hash(sq / 12, sq % 12 + 1); }
  void reset(size_t n) {
    table_.assign(n, EMPTY);
    fill_ = used_ = 0;
  }
  void place(size_t j, int sq) {
    table_[j] = sq;
    has_[sq] = true;
    ++fill_;
    ++used_;
    if (fill_ * 5 < (table_.size() - 1) * 3) return;
    resize(used_ > 50000 ? used_ * 2 : used_ * 4);
  }
  void insert_clean(int sq) {
    size_t mask = table_.size() - 1;
    uint64_t h = hash_of(sq);
    size_t i = h & mask;
    uint64_t perturb = h;
    while (true) {
      if (table_[i] == EMPTY) { table_[i] = sq; return; }
      if (i + 9 <= mask) {
        for (size_t j = 1; j <= 9; ++j)
          if (table_[i + j] == EMPTY) { table_[i + j] = sq; return; }
      }
      perturb >>= 5;
      i = (i * 5 + 1 + perturb) & mask;
    }
  }
  void resize(size_t minused) {
    size_t n = 8;
    while (n <= minused) n <<= 1;
    std::vector<int> old = table_;
    table_.assign(n, EMPTY);
    for (int k : old)
      if (k >= 0) insert_clean(k);
    fill_ = used_;
  }
};

// Modules/_randommodule.c
class PyRandom {
 public:
  explicit PyRandom(uint32_t seed) {
    init_genrand(19650218U);
    uint32_t key = seed;
    size_t i = 1, j = 0, k = N;
    for (; k; k--) {
      mt_[i] = (mt_[i] ^ ((mt_[i - 1] ^ (mt_[i - 1] >> 30)) * 1664525U)) + key + (uint32_t)j;
      i++; j++;
      if (i >= N) { mt_[0] = mt_[N - 1]; i = 1; }
      if (j >= 1) j = 0;
    }
    for (k = N - 1; k; k--) {
      mt_[i] = (mt_[i] ^ ((mt_[i - 1] ^ (mt_[i - 1] >> 30)) * 1566083941U)) - (uint32_t)i;
      i++;
      if (i >= N) { mt_[0] = mt_[N - 1]; i = 1; }
    }
    mt_[0] = 0x80000000U;
  }
  uint32_t genrand() {
    static const uint32_t mag01[2] = {0x0U, 0x9908b0dfU};
    uint32_t y;
    if (mti_ >= N) {
      size_t kk;
      for (kk = 0; kk < N - M; kk++) {
        y = (mt_[kk] & 0x80000000U) | (mt_[kk + 1] & 0x7fffffffU);
        mt_[kk] = mt_[kk + M] ^ (y >> 1) ^ mag01[y & 1U];
      }
      for (; kk < N - 1; kk++) {
        y = (mt_[kk] & 0x80000000U) | (mt_[kk + 1] & 0x7fffffffU);
        mt_[kk] = mt_[kk + (M - N)] ^ (y >> 1) ^ mag01[y & 1U];
      }
      y = (mt_[N - 1] & 0x80000000U) | (mt_[0] & 0x7fffffffU);
      mt_[N - 1] = mt_[M - 1] ^ (y >> 1) ^ mag01[y & 1U];
      mti_ = 0;
    }
    y = mt_[mti_++];
    y ^= (y >> 11);
    y ^= (y << 7) & 0x9d2c5680U;
    y ^= (y << 15) & 0xefc60000U;
    y ^= (y >> 18);
    return y;
  }
  uint32_t randbelow(uint32_t n) {   // n >= 1, n < 2^32
    int k = 0;
    while ((n >> k) != 0) ++k;     // n.bit_length()
    uint32_t r = genrand() >> (32 - k);
    while (r >= n) r = genrand() >> (32 - k);
    return r;
  }
  template <class T>
  void shuffle(std::vector<T>& x) {
    for (size_t i = x.size() - 1; i >= 1 && x.size() > 1; --i) {
      size_t j = randbelow((uint32_t)(i + 1));
      std::swap(x[i], x[j]);
      if (i == 1) break;
    }
  }

 private:
  static constexpr size_t N = 624, M = 397;
  uint32_t mt_[N];
  size_t mti_ = N + 1;
  void init_genrand(uint32_t s) {
    mt_[0] = s;
    for (mti_ = 1; mti_ < N; mti_++)
      mt_[mti_] = 1812433253U * (mt_[mti_ - 1] ^ (mt_[mti_ - 1] >> 30)) + (uint32_t)mti_;
  }
};

}  // namespace cp
