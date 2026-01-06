"""
Canonical Omega Delta operator (ΩΔ).

DUAL-AUDIENCE CONTRACT (NO CATEGORY MIXING)
===========================================

(A) Mathematical / Computer Science Contract (PRIMARY)
------------------------------------------------------
ΩΔ is the 2×2 Pauli-Z operator acting on a single-qubit Hilbert space:

    ΩΔ ≜ Z = [[ 1,  0 ],
              [ 0, -1 ]]

Formal invariants (provable, testable):
- Unitary:        Z† Z = I
- Involutory:     Z² = I
- Basis action:   Z|0⟩ = |0⟩,   Z|1⟩ = −|1⟩
- Eigenvalues:    {+1, −1} with eigenbasis {|0⟩, |1⟩}

Return convention (matrix form):
- omega_delta() returns the matrix as a pure-Python list-of-lists of complex.
  This keeps the operator dependency-free while remaining compatible with
  Qiskit Operator wrappers used in CI.

(B) Symbolic / Theological Contract (SECONDARY, METADATA)
---------------------------------------------------------
Within LucentTrinityOS, ΩΔ is the "Sealing" operator.

Symbolically, sealing denotes closure, marking, or covenantal boundary
application to a state transition.

Important constraints:
- This operator does NOT assert metaphysical proof.
- Mathematical correctness is independent of symbolic interpretation.
- The symbolic layer exists as metadata only.

Return convention (state form):
- omega_delta(state_dict) returns a shallow-copied dict with:
      state["op"] = "ΩΔ"
  This preserves legacy pipeline semantics without altering math behavior.
"""

from __future__ import annotations

from typing import Any, List, Optional

Matrix = List[List[complex]]


def omega_delta(state: Optional[Any] = None):
    # Matrix form (used by CI / Qiskit Operator wrapper)
    if state is None:
        return [[1 + 0j, 0j],
                [0j, -1 + 0j]]

    # Legacy "state transform" form (backwards compatibility)
    if isinstance(state, dict):
        state = dict(state)
        state["op"] = "ΩΔ"
        return state

    return state


__all__ = ["omega_delta"]
