CXX ?= g++
CXXFLAGS ?= -std=c++17 -O2 -Wall -Wextra
OUT := ../../../out/variant
VARIANTS := V1 V8 V6
TABLES := $(addprefix $(OUT)/tables/,$(addsuffix .txt,$(VARIANTS)))

all: $(OUT)/bfs $(OUT)/oracle $(OUT)/flagcheck tables

$(OUT)/bfs: $(addprefix $(OUT)/,bfs.o variant.o candidate.o)
	$(CXX) $(CXXFLAGS) -o $@ $^
$(OUT)/oracle: $(addprefix $(OUT)/,oracle.o variant.o candidate.o)
	$(CXX) $(CXXFLAGS) -o $@ $^
$(OUT)/flagcheck: $(addprefix $(OUT)/,flagcheck.o flags.o variant.o candidate.o)
	$(CXX) $(CXXFLAGS) -o $@ $^ -lpthread
$(OUT)/%.o: %.cpp variant.h candidate.h flags.h
	mkdir -p $(OUT)
	$(CXX) $(CXXFLAGS) -c $< -o $@
$(OUT)/tables/%.txt: ../export_tables.py ../bfs.py ../rules.py ../../count/candidates.py ../../count/filegame.py
	mkdir -p $(dir $@)
	python3 ../export_tables.py $* > $@.tmp
	mv $@.tmp $@
tables: $(TABLES)
clean:
	rm -f $(OUT)/*.o $(OUT)/bfs $(OUT)/oracle $(OUT)/flagcheck $(TABLES)
.PHONY: all tables clean
