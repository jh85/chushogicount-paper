// chu-plan: the planner and retro-relaxation of plan/planner.py and plan/relax.py in C++,
// driven over stdin by plan/cplanner.py.  One command per line, one reply line each.
//
//   plan <seed> <greedy|peel|edge|deps> <defer 0|1> <park 0|1> <end_turn B|W> <n> <sq:C:ROLE>...
//     -> "ok <usi>..." | "PlannerError\t<at>\t<phase>\t<reason>" | "Repetition\t<msg>"
//        | "Exception\t<type>\t<msg>"
//   relax <depth> <beam> <tries> <planner_retries> <turn B|W> <fix_turn 0|1> <n> <sq:C:ROLE>...
//     -> "ok <tried> <levels> <retracted> <base> <score> <usi>..." | "none <tried> <levels>"
//   certify <turn B|W> <n> <sq:C:ROLE>... <m> <usi>...   -> "ok <why>" | "fail <why>"
//   cand <n> <sq:C:ROLE>...   -> "1" | "0"  (is_candidate, PRIMARY setup, level file, colour)
//   mated <jcsa|lishogi> <turn B|W> <flag sq|-> <n> <sq:C:ROLE>...   -> "1" | "0"  (D13 mate)
//   mates <m> <usi>...   -> "ok <i>..." | "illegal <i> <i>..."  (plies whose position is mated,
//     replayed from the initial position under JCSA move rules; mate.h)
//   fixpair <turn B|W> <flag sq|-> <mv> <k> <na> <usi>... (<nb> <usi>...){na} <n> <sq:C:ROLE>...
//     -> "ok <i>,<j>..."  (mate.h fix_pairs, lishogi move legality as plan/engine.py)
// A target is a list of (square index x*12 + r-1, colour, role) in Python dict order.
#include <iostream>
#include <sstream>
#include <string>

#include "mate.h"
#include "planner.h"
#include "relax.h"

using namespace cp;

static OBoard read_target(std::istringstream& in) {
  int n;
  in >> n;
  OBoard t;
  for (int i = 0; i < n; ++i) {
    std::string tok;
    in >> tok;
    size_t a = tok.find(':'), b = tok.find(':', a + 1);
    int sq = std::stoi(tok.substr(0, a));
    int colour = tok[a + 1] == 'B' ? 0 : 1;
    std::string role = tok.substr(b + 1);
    int r = -1;
    for (int k = 0; k < NROLES; ++k)
      if (role == ROLE_NAME[k]) r = k;
    if (r < 0) throw std::runtime_error("bad role " + role);
    t.set(sq, mk(colour, r));
  }
  return t;
}

static std::string clean(std::string s) {
  for (char& c : s)
    if (c == '\n' || c == '\t') c = ' ';
  return s;
}

int main() {
  init_tables();
  std::ios::sync_with_stdio(false);
  Eng eng;
  std::string line;
  while (std::getline(std::cin, line)) {
    std::istringstream in(line);
    std::string cmd;
    in >> cmd;
    if (cmd.empty()) continue;
    if (cmd == "quit") break;
    std::string reply;
    try {
      if (cmd == "plan") {
        int seed, defer, park;
        std::string strat, et;
        in >> seed >> strat >> defer >> park >> et;
        OBoard t = read_target(in);
        Strategy st = strat == "greedy" ? Strategy::Greedy : strat == "peel" ? Strategy::Peel
                      : strat == "edge" ? Strategy::Edge : Strategy::Deps;
        try {
          Planner pl(t, eng, seed, et == "B" ? 0 : 1, st, defer != 0, park != 0);
          auto moves = pl.run();
          reply = "ok";
          for (auto& m : moves) reply += " " + m;
        } catch (PlannerError& e) {
          reply = "PlannerError\t" + (e.at < 0 ? std::string("-") : std::to_string(e.at)) + "\t" + clean(e.phase) +
                  "\t" + clean(e.reason);
        } catch (Repetition& e) {
          reply = "Repetition\t" + clean(e.msg);
        } catch (PyExc& e) {
          reply = "Exception\t" + e.type + "\t" + clean(e.msg);
        }
      } else if (cmd == "relax") {
        int depth, beam, tries, retries, fix;
        std::string tt;
        in >> depth >> beam >> tries >> retries >> tt >> fix;
        OBoard t = read_target(in);
        std::vector<std::string> moves;
        RelaxInfo info;
        if (relax(t, eng, depth, beam, tries, retries, tt == "B" ? 0 : 1, moves, info, fix != 0)) {
          reply = "ok " + std::to_string(info.tried) + " " + std::to_string(info.levels) + " " +
                  std::to_string(info.retracted) + " " + std::to_string(info.base) + " " + std::to_string(info.score);
          for (auto& m : moves) reply += " " + m;
        } else {
          reply = "none " + std::to_string(info.tried) + " " + std::to_string(info.levels);
        }
      } else if (cmd == "cand") {
        OBoard t = read_target(in);
        reply = is_candidate_primary(t.a) ? "1" : "0";
      } else if (cmd == "certify") {
        std::string tt;
        in >> tt;
        OBoard t = read_target(in);
        int m;
        in >> m;
        std::vector<std::string> moves(m);
        for (auto& s : moves) in >> s;
        std::string why;
        bool ok = certify(moves, t, tt == "B" ? 0 : 1, eng, &why);
        reply = (ok ? "ok " : "fail ") + why;
      } else if (cmd == "mated") {
        std::string rs, tt, fl;
        in >> rs >> tt >> fl;
        OBoard t = read_target(in);
        eng.set_board(t.a, tt == "B" ? 0 : 1, fl == "-" ? -1 : std::stoi(fl));
        reply = mated(eng.pos(), rs == "lishogi" ? chu::RuleSet::Lishogi : chu::RuleSet::JCSA) ? "1" : "0";
      } else if (cmd == "fixpair") {
        std::string tt, fl, mv;
        int k, na, nb;
        in >> tt >> fl >> mv >> k >> na;
        std::vector<std::string> as(na);
        for (auto& s : as) in >> s;
        std::vector<std::vector<std::string>> bs(na);
        for (auto& b : bs) {
          in >> nb;
          b.resize(nb);
          for (auto& s : b) in >> s;
        }
        OBoard t = read_target(in);
        eng.set_board(t.a, tt == "B" ? 0 : 1, fl == "-" ? -1 : std::stoi(fl));
        reply = "ok";
        for (auto [i, j] : fix_pairs(eng.pos(), mv, as, bs, k)) reply += " " + std::to_string(i) + "," + std::to_string(j);
      } else if (cmd == "mates") {
        int m;
        in >> m;
        std::vector<std::string> moves(m);
        for (auto& s : moves) in >> s;
        int illegal;
        std::vector<int> v = mate_plies(moves, &illegal);
        reply = illegal < 0 ? "ok" : "illegal " + std::to_string(illegal);
        for (int i : v) reply += " " + std::to_string(i);
      } else {
        reply = "error unknown command";
      }
    } catch (std::exception& e) {
      reply = std::string("error ") + clean(e.what());
    }
    std::cout << reply << "\n" << std::flush;
  }
  return 0;
}
