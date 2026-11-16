# All logs go to stdout; redirect to ../out/ when a persistent record is wanted.
all: build
setup:
	lake exe cache get
build:
	lake --no-ansi build
check:
	lake --no-ansi build ChuShogi.PlainFile ChuShogi.Specification
	lake env lean PackagingAudit.lean
audit: build
	lake env lean ReleaseAudit.lean
	lake env lean PromotionAudit.lean
counter: build
	lake env lean --run EfficientExecution.lean
certificate: build
	mkdir -p .lake/build/certification
	lake env lean -o .lake/build/certification/PrimaryCounts.olean certification/PrimaryCounts.lean
examples: build
	lake env lean --run EfficientBoardExecution.lean
.PHONY: all setup build check audit counter certificate examples
