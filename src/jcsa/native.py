"""Wrapper for the bundled v0.2.1 engine and its `rules <lishogi|jcsa>` protocol."""
import os
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
from plan.engine import Engine                                    # noqa: E402

NATIVE = os.environ.get("CHU_ENGINE_JCSA", str(Path(__file__).resolve().parent.parent.parent / "out" / "engine" / "chushogi-gen"))


class NativeEngine(Engine):
    def __init__(self, rules="lishogi", path=NATIVE):
        super().__init__(path)
        self.rules(rules)

    def rules(self, mode):
        out = self.ask(f"rules {mode}")
        assert out == "ok", f"rules {mode}: {out}"
        self.mode = mode
