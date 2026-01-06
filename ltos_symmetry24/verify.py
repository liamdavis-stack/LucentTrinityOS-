from __future__ import annotations

from dataclasses import dataclass
from typing import Dict, List

import numpy as np

from .golay import LinearCode24
from .symmetry import PermutationAction24


@dataclass(frozen=True)
class IntegrityReport:
    norm: float
    state_dim: int
    code_membership_possible: bool
    nearest_codeword_hamming_dist: int | None
    actions_verified: Dict[str, bool]


def nearest_codeword_distance(code: LinearCode24, bits24: np.ndarray) -> int:
    """Brute-force nearest Hamming distance to the code (OK for size 4096)."""
    b = np.array(bits24, dtype=int).reshape(-1) % 2
    if b.shape[0] != 24:
        raise ValueError("bits24 must be length 24.")
    # Hamming distances to all codewords
    diffs = (code.codewords ^ b)  # XOR over GF(2)
    dists = np.sum(diffs, axis=1)
    return int(np.min(dists))


def verify_actions_preserve_code(code: LinearCode24, actions: List[PermutationAction24]) -> Dict[str, bool]:
    """
    Verify each action preserves code membership for ALL codewords.
    Returns dict action_name -> bool.
    """
    results: Dict[str, bool] = {}
    for act in actions:
        ok = True
        for cw in code.codewords:
            permuted = cw[act.perm]
            if not code.contains(permuted):
                ok = False
                break
        results[act.name] = ok
    return results


def integrity_report(
    state24: np.ndarray,
    code: LinearCode24,
    actions: List[PermutationAction24],
    bits24_hint: np.ndarray | None = None,
) -> IntegrityReport:
    """
    LTOS-style integrity report.

    bits24_hint:
      - If you have a meaningful 24-bit encoding (e.g., axioms->bits), pass it in.
      - Otherwise, we skip nearest-codeword distance.
    """
    s = np.array(state24, dtype=complex).reshape(-1)
    norm = float(np.linalg.norm(s))
    dim = int(s.shape[0])

    membership_possible = True if code is not None else False

    nearest_dist = None
    if bits24_hint is not None and membership_possible:
        nearest_dist = nearest_codeword_distance(code, bits24_hint)

    action_results = verify_actions_preserve_code(code, actions) if membership_possible else {}
    return IntegrityReport(
        norm=norm,
        state_dim=dim,
        code_membership_possible=membership_possible,
        nearest_codeword_hamming_dist=nearest_dist,
        actions_verified=action_results,
    )
