"""
LucentTrinityOS - Kernel Layer
-----------------------------

Minimal execution kernel providing:
- registry access
- operator dispatch
- simulation routing
- canonical logging
- reproducible SHA256 sealing

This is the glue that binds the operator canon, registry ledger,
and simulation stack into a coherent OS-style execution environment.
"""

from __future__ import annotations

import hashlib
import json
import time
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Dict


DEFAULT_REGISTRY_PATH = Path("registry/ledger.log")
DEFAULT_CANON_LOG = Path("canon.log")


class KernelPanic(Exception):
    """Raised when the kernel encounters a non-recoverable state."""
    pass


@dataclass
class KernelPaths:
    registry_path: Path = DEFAULT_REGISTRY_PATH
    canon_log_path: Path = DEFAULT_CANON_LOG


class TrinityKernel:
    def __init__(self, paths: KernelPaths | None = None):
        self.boot_time = time.time()
        self.paths = paths or KernelPaths()

        # Ensure required dirs exist
        self.paths.registry_path.parent.mkdir(parents=True, exist_ok=True)

        # Ensure files exist
        self.paths.registry_path.touch(exist_ok=True)
        self.paths.canon_log_path.touch(exist_ok=True)

    # -------------------------------------------------------------
    # Logging + Sealing
    # -------------------------------------------------------------
    def seal(self, payload: Dict[str, Any]) -> str:
        """Return a SHA256 seal for a canonical payload."""
        encoded = json.dumps(payload, sort_keys=True, separators=(",", ":")).encode("utf-8")
        return hashlib.sha256(encoded).hexdigest()

    def log_canon(self, message: str) -> None:
        """Append a canonical event to canon.log."""
        stamp = time.strftime("%Y-%m-%d %H:%M:%S", time.localtime())
        with self.paths.canon_log_path.open("a", encoding="utf-8") as f:
            f.write(f"[{stamp}] {message}\n")

    # -------------------------------------------------------------
    # Registry Interaction
    # -------------------------------------------------------------
    def write_registry(self, entry: Dict[str, Any]) -> str:
        """
        Append a structured entry to the registry ledger.
        Returns the seal.
        """
        to_seal = dict(entry)
        to_seal["timestamp"] = time.time()
        seal = self.seal(to_seal)

        record = dict(to_seal)
        record["seal"] = seal

        with self.paths.registry_path.open("a", encoding="utf-8") as f:
            f.write(json.dumps(record, separators=(",", ":")) + "\n")

        self.log_canon(f"Registry entry sealed: {seal}")
        return seal

    def registry_count(self) -> int:
        with self.paths.registry_path.open("r", encoding="utf-8") as f:
            return sum(1 for _ in f)

    # -------------------------------------------------------------
    # Operator Dispatch
    # -------------------------------------------------------------
    def dispatch_operator(self, name: str, *args: Any, **kwargs: Any) -> Any:
        """
        Dynamically load and execute an operator from src/operators.

        Convention:
        - module: src/operators/<name>.py
        - callable: def <name>(...) -> ...
        """
        try:
            module = __import__(f"src.operators.{name}", fromlist=[name])
        except ImportError as e:
            raise KernelPanic(f"Operator '{name}' not found") from e

        if not hasattr(module, name):
            raise KernelPanic(f"Operator function '{name}' missing in module")

        op = getattr(module, name)
        result = op(*args, **kwargs)

        self.write_registry({
            "event": "operator_dispatch",
            "operator": name,
            "args": list(args),   # JSON-friendly
            "kwargs": kwargs
        })

        return result

    # -------------------------------------------------------------
    # Boot + Status
    # -------------------------------------------------------------
    def boot(self) -> Dict[str, Any]:
        self.log_canon("LucentTrinity
