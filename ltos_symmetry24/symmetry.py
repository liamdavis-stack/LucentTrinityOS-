from __future__ import annotations

from dataclasses import dataclass
from typing import List

import numpy as np


@dataclass(frozen=True)
class PermutationAction24:
    """A code-preserving permutation action on 24 coordinates."""
    name: str
    perm: np.ndarray  # shape (24,), dtype int, a permutation of 0..23

    def apply_to_bits(self, bits24: np.ndarray) -> np.ndarray:
        b = np.array(bits24, dtype=int).reshape(-1)
        if b.shape[0] != 24:
            raise ValueError("bits24 must be length 24.")
        return b[self.perm]

    def apply_to_state(self, state24: np.ndarray) -> np.ndarray:
        s = np.array(state24, dtype=complex).reshape(-1)
        if s.shape[0] != 24:
            raise ValueError("state24 must be length 24.")
        return s[self.perm]


def default_actions() -> List[PermutationAction24]:
    """
    Default symmetry actions.

    NOTE:
    These are NOT claimed to be M24 generators.
    They are merely example permutations you can verify preserve your code set.
    Replace/add actions once you have verified generators.
    """
    gen1 = np.array([1,2,3,4,5,6,7,0, 8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23], dtype=int)
    gen2 = np.array([0,1,2,3,4,5,6,7, 9,10,11,8,13,14,15,12,17,18,19,16,21,22,23,20], dtype=int)
    return [
        PermutationAction24(name="perm_shift_0_7", perm=gen1),
        PermutationAction24(name="perm_block_swap", perm=gen2),
    ]
