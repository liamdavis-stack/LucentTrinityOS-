"""
Theta-Entanglement Exchange Operator (Θᴱ) — iSH-safe (no NumPy)

Canonical semantics:
- Acts on H_A ⊗ H_B ⊗ H_C ⊗ H_D with each subsystem dimension d.
- Implemented as the unitary wire permutation SWAP_{B,C}.
- This is a concrete witness for the family-mapping AB|CD -> AC|BD on
  pair-factorized inputs, without measurement or post-selection.

Kernel contract:
- Module name == callable name for dispatch:
  theta_entanglement_exchange(...)
"""

from __future__ import annotations

from typing import Any, Dict, Iterable, List, Sequence

from .base import OperatorResult


def _as_complex_list(state: Any) -> List[complex]:
    """
    Accept either:
      - a sequence of numbers (complex/float/int), or
      - a dict containing {'psi': sequence}
    Return a flat list[complex].
    """
    if isinstance(state, dict) and "psi" in state:
        seq = state["psi"]
    else:
        seq = state

    if not isinstance(seq, (list, tuple)):
        seq = list(seq)  # allow iterables

    out: List[complex] = []
    for x in seq:
        out.append(complex(x))
    if len(out) == 0:
        raise ValueError("state vector is empty")
    return out


def _swap_BC(psi: Sequence[complex], d: int) -> List[complex]:
    """
    Apply SWAP between subsystems B and C on a 4-partite statevector.

    Index convention: flatten indices in A,B,C,D order:
      idx = (((a*d + b)*d + c)*d + dd)

    After SWAP_{B,C}:
      (a,b,c,dd) -> (a,c,b,dd)
    """
    if d < 2:
        raise ValueError("dim must be >= 2")
    n = d ** 4
    if len(psi) != n:
        raise ValueError(f"state length must be d^4={n}, got {len(psi)}")

    out = [0j] * n
    for a in range(d):
        for b in range(d):
            for c in range(d):
                for dd in range(d):
                    i = (((a * d + b) * d + c) * d + dd)
                    j = (((a * d + c) * d + b) * d + dd)
                    out[j] = psi[i]
    return out


def theta_entanglement_exchange(
    state: Any,
    dim: int = 2,
    pattern: str = "(A,B)|(C,D)->(A,C)|(B,D)",
) -> OperatorResult:
    """
    Θᴱ kernel entrypoint.

    Parameters
    ----------
    state:
      - vector: length d^4, or
      - dict with key 'psi' containing that vector.
    dim:
      dimension d of each subsystem.
    pattern:
      currently only supports the canonical exchange:
        (A,B)|(C,D)->(A,C)|(B,D)

    Returns
    -------
    OperatorResult(before, after, name, meta)
    """
    if pattern != "(A,B)|(C,D)->(A,C)|(B,D)":
        raise ValueError("Unsupported pattern. Supported: '(A,B)|(C,D)->(A,C)|(B,D)'")

    psi = _as_complex_list(state)
    out = _swap_BC(psi, int(dim))

    meta: Dict[str, Any] = {
        "symbol": "Θᴱ",
        "dim": int(dim),
        "pattern": pattern,
        "witness": "SWAP_{B,C}",
        "notes": "iSH-safe pure-Python implementation (no NumPy)",
    }

    # Keep state shape stable: if input was dict{'psi':...}, return dict too.
    if isinstance(state, dict) and "psi" in state:
        after = dict(state)
        after["psi"] = out
        return OperatorResult(before=state, after=after, name="ThetaEntanglementExchange", meta=meta)

    return OperatorResult(before=psi, after=out, name="ThetaEntanglementExchange", meta=meta)
