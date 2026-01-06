import math
import random

from src.axiom_engine.operators.theta_entanglement_exchange import (
    theta_entanglement_exchange,
)

# -------------------------
# Helpers (pure Python)
# -------------------------

def _norm(v):
    return math.sqrt(sum((x.conjugate() * x).real for x in v))

def _normalize(v):
    n = _norm(v)
    if n == 0:
        raise ValueError("zero vector")
    return [x / n for x in v]

def _vdot(a, b):
    # conjugate dot product
    return sum(x.conjugate() * y for x, y in zip(a, b))

def _kron(a, b):
    out = []
    for x in a:
        for y in b:
            out.append(x * y)
    return out

def _bell_phi_plus():
    # |Φ+> = (|00> + |11>)/sqrt(2)
    s = 1.0 / math.sqrt(2.0)
    v = [0j] * 4
    v[0] = complex(s, 0.0)
    v[3] = complex(s, 0.0)
    return v

def _rand_state(n, seed=0):
    rng = random.Random(seed)
    v = []
    for _ in range(n):
        re = rng.gauss(0.0, 1.0)
        im = rng.gauss(0.0, 1.0)
        v.append(complex(re, im))
    return _normalize(v)

def _swap_BC_reference(psi, d):
    # Same mapping as operator: (a,b,c,dd)->(a,c,b,dd)
    out = [0j] * (d**4)
    for a in range(d):
        for b in range(d):
            for c in range(d):
                for dd in range(d):
                    i = (((a*d + b)*d + c)*d + dd)
                    j = (((a*d + c)*d + b)*d + dd)
                    out[j] = psi[i]
    return out

def _rank1_check_AC_BD(psi, d, tol=1e-10):
    """
    Check if psi factors across (AC)|(BD) without SVD.

    Build matrix M of shape (d^2) x (d^2) where:
      row = (a,c), col = (b,dd), and amplitudes are in A,B,C,D ordering.

    Rank-1 condition: for all i,j:
      M[i][j] * M[r0][c0] == M[i][c0] * M[r0][j]
    for some pivot (r0,c0) where M[r0][c0] != 0.
    """
    # build M as list of lists
    N = d*d
    M = [[0j for _ in range(N)] for __ in range(N)]

    for a in range(d):
        for b in range(d):
            for c in range(d):
                for dd in range(d):
                    idx = (((a*d + b)*d + c)*d + dd)
                    r = a*d + c       # (a,c)
                    col = b*d + dd    # (b,dd)
                    M[r][col] = psi[idx]

    # find pivot
    r0 = c0 = None
    pivot = 0j
    for r in range(N):
        for c in range(N):
            if abs(M[r][c]) > tol:
                r0, c0 = r, c
                pivot = M[r][c]
                break
        if r0 is not None:
            break

    if r0 is None:
        # near-zero state (shouldn't happen in tests)
        return False

    # rank-1 minors check
    for r in range(N):
        for c in range(N):
            lhs = M[r][c] * pivot
            rhs = M[r][c0] * M[r0][c]
            if abs(lhs - rhs) > tol:
                return False
    return True


# -------------------------
# Tests
# -------------------------

def test_theta_preserves_norm_and_shape_qubits():
    d = 2
    psi = _rand_state(d**4, seed=123)

    res = theta_entanglement_exchange(psi, dim=d)
    out = res.after

    assert isinstance(out, list)
    assert len(out) == d**4
    assert abs(_norm(out) - 1.0) < 1e-12

def test_theta_matches_reference_swap():
    d = 2
    psi = _rand_state(d**4, seed=7)

    res = theta_entanglement_exchange(psi, dim=d)
    out = res.after

    ref = _swap_BC_reference(psi, d)
    # up to exact equality for pure permutation
    assert out == ref

def test_theta_maps_pair_factorized_inputs_to_AC_BD_factorized():
    d = 2
    phi_ab = _rand_state(d*d, seed=1)
    chi_cd = _rand_state(d*d, seed=2)
    psi = _kron(phi_ab, chi_cd)  # AB|CD product

    res = theta_entanglement_exchange(psi, dim=d)
    out = res.after

    assert _rank1_check_AC_BD(out, d=d, tol=1e-10)

