"""
Canonical Omega Delta operator.

Dual-mode:
- If called with no args: returns the 2x2 matrix (Pauli-Z) as complex list-lists.
- If called with a state object (e.g. dict): applies metadata / tag to state (legacy behavior).
"""

from __future__ import annotations

from typing import Any, List, Optional

Matrix = List[List[complex]]


def omega_delta(state: Optional[Any] = None):
    # Matrix form (used by CI/Qiskit Operator wrapper)
    if state is None:
        return [[1 + 0j, 0j],
                [0j, -1 + 0j]]

    # Legacy "state transform" form (keep backwards compat with your earlier pipeline style)
    if isinstance(state, dict):
        state = dict(state)
        state["op"] = "ΩΔ"
        return state

    return state


__all__ = ["omega_delta"]
