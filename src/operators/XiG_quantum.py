"""
Legacy quantum operator (CI/tests).
Provides a simple 1-qubit unitary matrix for XiΓ.
"""

import numpy as np

def XiG_quantum():
    # Identity gate (unitary)
    return np.eye(2, dtype=complex)

__all__ = ["XiG_quantum"]
