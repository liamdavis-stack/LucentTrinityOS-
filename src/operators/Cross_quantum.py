"""
Legacy quantum operator (CI/tests).
Implements a 3-qubit SWAP between qubit-0 and qubit-2 as "Cross".
Self-inverse (U == U^-1) and unitary.
"""

import numpy as np

def _swap_q0_q2_3qubit():
    # Basis ordering |q0 q1 q2> in binary 0..7
    U = np.zeros((8, 8), dtype=complex)
    for i in range(8):
        q0 = (i >> 2) & 1
        q1 = (i >> 1) & 1
        q2 = (i >> 0) & 1
        j = (q2 << 2) | (q1 << 1) | (q0 << 0)  # swap q0 and q2
        U[j, i] = 1.0
    return U

def Cross_quantum():
    return _swap_q0_q2_3qubit()

def Cross_inverse_quantum():
    # SWAP is its own inverse
    return _swap_q0_q2_3qubit()

__all__ = ["Cross_quantum", "Cross_inverse_quantum"]
