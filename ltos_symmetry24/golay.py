from __future__ import annotations

from dataclasses import dataclass
from itertools import product
from typing import Iterable, Tuple

import numpy as np


def _bits_to_int(bits: np.ndarray) -> int:
    """Pack a length-24 binary vector into an int (little-endian)."""
    # bits assumed 0/1 ints length 24
    out = 0
    for i, b in enumerate(bits.tolist()):
        out |= (int(b) & 1) << i
    return out


@dataclass(frozen=True)
class LinearCode24:
    """A small utility wrapper for a binary linear code in {0,1}^24."""
    generator_matrix: np.ndarray  # shape (k,24), dtype int (0/1)
    codewords: np.ndarray         # shape (2^k, 24), dtype int (0/1)
    codeword_ints: frozenset[int] # packed representation for fast membership

    @property
    def n(self) -> int:
        return 24

    @property
    def k(self) -> int:
        return int(self.generator_matrix.shape[0])

    def contains(self, word: np.ndarray) -> bool:
        w = np.array(word, dtype=int).reshape(-1) % 2
        if w.shape[0] != 24:
            return False
        return _bits_to_int(w) in self.codeword_ints

    def hamming_weight(self, word: np.ndarray) -> int:
        w = np.array(word, dtype=int).reshape(-1) % 2
        return int(np.sum(w))


def generate_code_from_generator(G: np.ndarray) -> LinearCode24:
    """
    Generate all codewords from a kx24 generator matrix G over GF(2).
    Produces 2^k codewords.
    """
    G = np.array(G, dtype=int) % 2
    if G.ndim != 2 or G.shape[1] != 24:
        raise ValueError("Generator matrix must be shape (k,24).")
    k = G.shape[0]

    # Enumerate all messages in {0,1}^k
    msgs = np.array(list(product([0, 1], repeat=k)), dtype=int)  # (2^k, k)
    codewords = (msgs @ G) % 2  # (2^k, 24)

    codeword_ints = frozenset(_bits_to_int(c) for c in codewords)
    return LinearCode24(generator_matrix=G, codewords=codewords, codeword_ints=codeword_ints)


def default_golay_like_generator() -> np.ndarray:
    """
    Default 12x24 generator matrix placeholder.

    IMPORTANT:
    - This may or may not be the *standard extended Golay* generator matrix.
    - LTOS uses it as a deterministic code substrate unless you swap it for a verified reference.

    You can replace this function with a known-good standard generator later.
    """
    G = np.array([
        [1,0,0,0,0,0,0,0,0,0,0,0, 1,1,1,1,1,1,1,1,1,1,1,1],
        [0,1,0,0,0,0,0,0,0,0,0,0, 1,1,1,1,0,0,0,0,1,1,1,1],
        [0,0,1,0,0,0,0,0,0,0,0,0, 1,1,0,0,1,1,0,0,1,1,1,1],
        [0,0,0,1,0,0,0,0,0,0,0,0, 1,0,1,0,1,0,1,0,1,0,1,1],
        [0,0,0,0,1,0,0,0,0,0,0,0, 0,1,1,0,0,1,1,0,1,1,0,1],
        [0,0,0,0,0,1,0,0,0,0,0,0, 0,1,0,1,0,1,0,1,1,0,1,1],
        [0,0,0,0,0,0,1,0,0,0,0,0, 0,0,1,1,0,0,1,1,1,0,1,1],
        [0,0,0,0,0,0,0,1,0,0,0,0, 1,0,0,1,1,0,0,1,1,1,0,1],
        [0,0,0,0,0,0,0,0,1,0,0,0, 1,1,0,1,1,1,0,0,1,0,1,1],
        [0,0,0,0,0,0,0,0,0,1,0,0, 1,1,1,0,1,0,1,0,0,1,1,1],
        [0,0,0,0,0,0,0,0,0,0,1,0, 1,0,1,1,1,0,0,1,0,1,1,1],
        [0,0,0,0,0,0,0,0,0,0,0,1, 0,1,1,1,1,0,1,1,0,0,1,1],
    ], dtype=int)
    return G
