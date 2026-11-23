# Separate reference checker; links the pinned engine sources unchanged.
CXX ?= g++
CXXFLAGS ?= -O2 -std=c++17 -Wall -Wextra
ENG := ../../../out/engine/src
ENGSRC := $(ENG)/types.cpp $(ENG)/position.cpp $(ENG)/sfen.cpp $(ENG)/usi.cpp $(ENG)/movegen.cpp $(ENG)/status.cpp
BIN := ../../../out/bin/jcsa-native-audit

$(BIN): main.cpp $(ENGSRC) $(wildcard $(ENG)/*.h)
	mkdir -p ../../../out/bin
	$(CXX) $(CXXFLAGS) -I$(ENG) -o $@ main.cpp $(ENGSRC)

.PHONY: all
all: $(BIN)
