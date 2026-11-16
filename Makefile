ENGINE_REV := 1a941d5a7460bdc01de253eb3e5b80a598d1eb1a
ENGINE_DIR := out/engine
PYTHON ?= python3

all: engine planner variants fixtures

# The public tag is checked against its immutable commit before compilation.
setup:
	mkdir -p out
	@if ! test -d $(ENGINE_DIR); then GIT_TERMINAL_PROMPT=0 git -c credential.helper= clone --depth 1 --branch v0.2.1 https://github.com/jh85/chushogi.git $(ENGINE_DIR); fi
	@test "$$(git -C $(ENGINE_DIR) rev-parse HEAD)" = "$(ENGINE_REV)" || { echo 'Engine revision mismatch; preserve local work and use the pinned v0.2.1 revision.'; exit 1; }

engine: setup
	$(MAKE) -C $(ENGINE_DIR)
planner: engine
	$(MAKE) -C src/plan/cpp
variants:
	$(MAKE) -C src/variant/cpp
fixtures: engine
	$(PYTHON) tests/jcsa_cases/build.py

test: all
	$(PYTHON) tests/test_count.py
	$(PYTHON) tests/test_mobility.py
	$(PYTHON) tests/test_sampler.py
	$(PYTHON) tests/test_jcsa.py
	$(PYTHON) tests/test_cmate.py --boards 4 --flagged 0 --games 0 --cand 0 --procs 1
	$(PYTHON) tests/test_variant_cpp.py --n 30 --depth 2

.PHONY: all setup engine planner variants fixtures test
