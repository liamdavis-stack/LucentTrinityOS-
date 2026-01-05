"""
Legacy quantum operator (CI/tests).
Provides a simple 1-qubit unitary matrix for OmegaΔ.
"""

import numpy as np

def OmegaD_quantum():
    # Pauli-Z gate (unitary): [[1,0],[0,-1]]
    return np.array([[1, 0],
                     [0, -1]], dtype=complex)

__all__ = ["OmegaD_quantum"]
