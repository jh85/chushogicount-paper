# Provenance and retained licenses

Original code in this repository is licensed under Apache License 2.0; see
[LICENSE](LICENSE). The following material retains its own terms. Existing
source comments and attribution notices are preserved.

## Author-owned engine and rule references

Chushogi (`jh85/chushogi`) is the author's own repository, not third-party code
merely because setup fetches it separately. The pin is v0.2.1, commit
`1a941d5a7460bdc01de253eb3e5b80a598d1eb1a`. The adapted board renderer is also
from that author-owned project.

Lishogi/scalashogi was consulted as a reference for interpreting ambiguous chu
shogi rules. The author confirms that no Lishogi source code was incorporated.
Historical engine comments describing code as “ported” are preserved as
existing records, not treated as evidence of incorporated Lishogi source.
JCSA rule pages are references too; their pages/images are not bundled.

The fetched engine does identify externally sourced **test data**:
`tests/perft_test.py` and its README identify positions/counts in
`tests/perft_cases.tsv` as extracted from scalashogi fixtures;
`tests/status_test.py` identifies additional scalashogi test positions. These
are distinct from engine source-code provenance. The scalashogi MIT notice is
retained below. These fixtures are fetched dependencies, not this repository's
Git payload. Other downloaded-game data in the engine is not relicensed by
this project's Apache grant.

### Separate Chushogi licensing clarification

The pinned snapshot contains no LICENSE, COPYING or NOTICE file. This project's
grant covers original material in this repository; it does not automatically
license the separately fetched engine. No original repository was modified.

The needed follow-up in Chushogi is an explicit grant covering its original
code at `1a941d5a7460bdc01de253eb3e5b80a598d1eb1a`: add the standard Apache-2.0
LICENSE and a README statement expressly covering that earlier snapshot.
Retain the scalashogi fixture attribution/MIT notice and other applicable
external terms. If setup is repinned to a new licensed commit, update the exact
commit and tag together without moving the existing release tag. An explicit
grant covering the existing snapshot can clarify it without changing this pin.

## Incorporated compatibility routines

`src/plan/cpp/pycompat.h` explicitly references CPython's `Objects/tupleobject.c`,
`Objects/setobject.c` and `Modules/_randommodule.c`. Source comparison identifies
C++ adaptations of the tuple hash, set behavior and MT19937 initialization/twist
routines. Upstream notices are retained for these compatibility portions rather
than describing them as Apache-only original code.

CPython portions retain PSF License Version 2; MT19937 retains the
Matsumoto/Nishimura notice. Modifications specialize the routines to C++ classes,
square-index keys and 32-bit seeds, remove Python object/runtime interfaces,
and add planner compatibility behavior. Original project additions are
Apache-2.0, subject to retained upstream terms. No incompatible terms were found.

Sources inspected: [CPython 3.14.4 license](https://github.com/python/cpython/blob/v3.14.4/LICENSE),
[MT19937 notice](https://github.com/python/cpython/blob/v3.14.4/Modules/_randommodule.c),
[scalashogi license](https://github.com/WandererXII/scalashogi/blob/master/LICENSE).

## External dependencies

Python/CPython, Lean, Mathlib and transitive packages, optional Pillow and CJK
fonts retain their own licenses/notices; none is relicensed here. Locked
revisions remain in `lean/lake-manifest.json`, and setup leaves fetched
license/notice files intact. Inspected Mathlib/transitive LICENSE files are
Apache-2.0 except `Cli` (MIT). The Lean toolchain and optional packages may have
additional component notices; preserve their supplied distributions when
redistributing them. No dependency licenses or pins were changed.

## Retained PSF license

Copyright (c) 2001 Python Software Foundation; All Rights Reserved.

```text
PYTHON SOFTWARE FOUNDATION LICENSE VERSION 2
--------------------------------------------

1. This LICENSE AGREEMENT is between the Python Software Foundation
("PSF"), and the Individual or Organization ("Licensee") accessing and
otherwise using this software ("Python") in source or binary form and
its associated documentation.

2. Subject to the terms and conditions of this License Agreement, PSF hereby
grants Licensee a nonexclusive, royalty-free, world-wide license to reproduce,
analyze, test, perform and/or display publicly, prepare derivative works,
distribute, and otherwise use Python alone or in any derivative version,
provided, however, that PSF's License Agreement and PSF's notice of copyright,
i.e., "Copyright (c) 2001 Python Software Foundation; All Rights Reserved"
are retained in Python alone or in any derivative version prepared by Licensee.

3. In the event Licensee prepares a derivative work that is based on
or incorporates Python or any part thereof, and wants to make
the derivative work available to others as provided herein, then
Licensee hereby agrees to include in any such work a brief summary of
the changes made to Python.

4. PSF is making Python available to Licensee on an "AS IS"
basis.  PSF MAKES NO REPRESENTATIONS OR WARRANTIES, EXPRESS OR
IMPLIED.  BY WAY OF EXAMPLE, BUT NOT LIMITATION, PSF MAKES NO AND
DISCLAIMS ANY REPRESENTATION OR WARRANTY OF MERCHANTABILITY OR FITNESS
FOR ANY PARTICULAR PURPOSE OR THAT THE USE OF PYTHON WILL NOT
INFRINGE ANY THIRD PARTY RIGHTS.

5. PSF SHALL NOT BE LIABLE TO LICENSEE OR ANY OTHER USERS OF PYTHON
FOR ANY INCIDENTAL, SPECIAL, OR CONSEQUENTIAL DAMAGES OR LOSS AS
A RESULT OF MODIFYING, DISTRIBUTING, OR OTHERWISE USING PYTHON,
OR ANY DERIVATIVE THEREOF, EVEN IF ADVISED OF THE POSSIBILITY THEREOF.

6. This License Agreement will automatically terminate upon a material
breach of its terms and conditions.

7. Nothing in this License Agreement shall be deemed to create any
relationship of agency, partnership, or joint venture between PSF and
Licensee.  This License Agreement does not grant permission to use PSF
trademarks or trade name in a trademark sense to endorse or promote
products or services of Licensee, or any third party.

8. By copying, installing or otherwise using Python, Licensee
agrees to be bound by the terms and conditions of this License
Agreement.
```

## Retained MT19937 notice

```text
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
```

## Retained scalashogi fixture notice

```text
Copyright (c) 2012-2014 Thibault Duplessis

The MIT license

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is furnished
to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
THE SOFTWARE.
```
