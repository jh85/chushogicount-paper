# C++ planner, linked against the public pinned engine fetched by root `make setup`.
CXX ?= g++
CXXFLAGS ?= -O2 -std=c++17 -Wall -Wextra
ENG ?= ../../../out/engine/src
BIN := ../../../out/bin/chu-plan
ENGSRC := $(ENG)/types.cpp $(ENG)/position.cpp $(ENG)/sfen.cpp $(ENG)/usi.cpp $(ENG)/movegen.cpp $(ENG)/status.cpp
SRC := core.cpp filegame.cpp eng.cpp planner.cpp relax.cpp mate.cpp main.cpp
HDR := core.h filegame.h eng.h planner.h relax.h mate.h pycompat.h

$(BIN): $(SRC) $(HDR) $(ENGSRC)
	mkdir -p $(dir $@)
	$(CXX) $(CXXFLAGS) -o $@ $(SRC) $(ENGSRC)

clean:
	rm -f $(BIN)
.PHONY: clean
