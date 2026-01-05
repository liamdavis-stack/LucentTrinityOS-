"""
Canonical Cross operator (3-qubit cyclic permutation).

Definition:
    Cross |a b c> = |b c a>
So it is an 8x8 permutation unitary (order 3).
"""

from __future__ import annotations

from typing import List

Matrix = List[List[complex]]


def _idx(a: int, b: int, c: int) -> int:
    return (a << 2) | (b << 1) | c


def _zero(n: int) -> Matrix:
    return [[0j for _ in range(n)] for _ in range(n)]


def cross() -> Matrix:
    """Return the 8x8 unitary matrix for the cyclic shift |a b c> -> |b c a|."""
    n = 8
    U = _zero(n)
    for a in (0, 1):
        for b in (0, 1):
            for c in (0, 1):
                inp = _idx(a, b, c)
                out = _idx(b, c, a)
                U[out][inp] = 1 + 0j
    return U


def cross_inverse() -> Matrix:
    """Inverse of cross: |a b c> -> |c a b| (i.e., cross^2)."""
    n = 8
    U = _zero(n)
    for a in (0, 1):
        for b in (0, 1):
            for c in (0, 1):
                inp = _idx(a, b, c)
                out = _idx(c, a, b)
                U[out][inp] = 1 + 0j
    return U


__all__ = ["cross", "cross_inverse"]
