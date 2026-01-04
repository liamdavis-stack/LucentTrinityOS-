import numpy as np

def Cross_quantum():
    """
    Cross operator defined by:
        Cross |a b c> = |b c a>
    using the same basis ordering as _ket3 in validation tests.
    """
    U = np.zeros((8, 8), dtype=complex)

    def idx(a, b, c):
        return (a << 2) | (b << 1) | c

    for a in (0, 1):
        for b in (0, 1):
            for c in (0, 1):
                U[idx(b, c, a), idx(a, b, c)] = 1.0

    return U

def Cross_inverse_quantum():
    """
    Inverse of Cross operator:
        Cross^{-1} |a b c> = |c a b>
    Using the same basis ordering as _ket3 in validation tests.
    """
    U = np.zeros((8, 8), dtype=complex)

    def idx(a, b, c):
        return (a << 2) | (b << 1) | c

    for a in (0, 1):
        for b in (0, 1):
            for c in (0, 1):
                U[idx(c, a, b), idx(a, b, c)] = 1.0

    return U
