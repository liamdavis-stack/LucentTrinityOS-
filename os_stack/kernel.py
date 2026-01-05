from __future__ import annotations

import json
import time
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Dict, List
import importlib


OptionalState = Dict[str, Any]


class KernelPanic(RuntimeError):
    pass


@dataclass
class DispatchRecord:
    event: str
    operator: str
    ts: float
    args: List[Any]
    kwargs: Dict[str, Any]


class TrinityKernel:
    """
    Minimal, paste-safe kernel for iSH.
    - Discovers operators from the package directory
    - Dispatches by importing module and calling function of same name
    - Logs canon + registry ledger
    """

    OPERATOR_PACKAGE = "src.axiom_engine.operators"

    def __init__(self, repo_root: Path | None = None) -> None:
        self.repo_root = (repo_root or Path(__file__).resolve().parents[1]).resolve()

        self.registry_dir = (self.repo_root / "registry").resolve()
        self.registry_dir.mkdir(parents=True, exist_ok=True)

        self.ledger_path = self.registry_dir / "ledger.log"
        self.canon_path = self.repo_root / "canon.log"

        self._operators_dir = self._resolve_package_dir(self.OPERATOR_PACKAGE)

    def _resolve_package_dir(self, pkg: str) -> Path:
        """Resolve a package directory safely in iSH.

        Avoids importlib.util (can be missing or shadowed). Uses __import__ and __file__.
        """
        try:
            mod = __import__(pkg, fromlist=["__file__"])
        except Exception as e:
            raise KernelPanic(f"Cannot import operator package '{pkg}': {e}") from e

        mod_file = getattr(mod, "__file__", None)
        if not mod_file:
            raise KernelPanic(f"Operator package '{pkg}' has no __file__ (unexpected)")

        return Path(mod_file).resolve().parent

    def list_operators(self) -> List[str]:
        if not self._operators_dir.exists():
            raise KernelPanic(f"Operators directory not found: {self._operators_dir}")

        ops: List[str] = []
        for p in sorted(self._operators_dir.glob("*.py")):
            name = p.stem
            if name.startswith("_"):
                continue
            ops.append(name)
        return ops

    def log_canon(self, message: str) -> None:
        line = f"{time.time():.3f} {message}\n"
        with self.canon_path.open("a", encoding="utf-8") as f:
            f.write(line)

    def write_registry(self, record: DispatchRecord) -> None:
        with self.ledger_path.open("a", encoding="utf-8") as f:
            f.write(json.dumps(record.__dict__) + "\n")

    def dispatch_operator(self, name: str, *args: Any, **kwargs: Any) -> Any:
        available = set(self.list_operators())
        if name not in available:
            raise KernelPanic(f"Operator '{name}' not found. Available: {sorted(available)}")

        module_path = f"{self.OPERATOR_PACKAGE}.{name}"
        try:
            module = importlib.import_module(module_path)
        except Exception as e:
            raise KernelPanic(f"Failed to import operator module: {module_path}") from e

        if not hasattr(module, name):
            raise KernelPanic(f"Function '{name}' missing in operator module")

        fn = getattr(module, name)
        result = fn(*args, **kwargs)

        self.write_registry(
            DispatchRecord(
                event="operator_dispatch",
                operator=name,
                ts=time.time(),
                args=list(args),
                kwargs=kwargs,
            )
        )
        return result

    def boot(self) -> Dict[str, Any]:
        ops = self.list_operators()
        self.log_canon(f"LucentTrinityOS boot OK | operators={ops}")
        return {"status": "ok", "operators": ops}
