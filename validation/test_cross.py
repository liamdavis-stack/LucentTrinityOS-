import numpy as np
from itertools import product
from qiskit.quantum_info import Operator

from src.operators.Cross_quantum import Cross_quantum, Cross_inverse_quantum


def _ket3(a: int, b: int, c: int) -> np.ndarray:
    """
    Build computational basis ket |a b c> as an 8-vector.
    Index convention: |q0 q1 q2> -> (a<<2) | (b<<1) | c
    """
    idx = (a << 2) | (b << 1) | c
    v = np.zeros(8, dtype=complex)
    v[idx] = 1.0
    return v


def test_cross_is_unitary():
    U = Operator(Cross_quantum()).data
    I = np.eye(8, dtype=complex)
    assert np.allclose(U.conj().T @ U, I)


def test_cross_has_order_three():
    U = Operator(Cross_quantum()).data
    I = np.eye(8, dtype=complex)
    assert np.allclose(U @ U @ U, I)


def test_cross_inverse_is_cross_squared():
    U = Operator(Cross_quantum()).data
    Uinv = Operator(Cross_inverse_quantum()).data
    assert np.allclose(Uinv, U @ U)


def test_cross_basis_mapping():
    """
    Definition check:
        Cross |a b c> = |b c a>
    """
    U = Operator(Cross_quantum()).data
    for a, b, c in product([0, 1], repeat=3):
        inp = _ket3(a, b, c)
        out = U @ inp
        exp = _ket3(b, c, a)
        assert np.allclose(out, exp)
