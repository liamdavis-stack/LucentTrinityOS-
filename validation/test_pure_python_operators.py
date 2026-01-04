from itertools import product

def matmul(A, B):
    n, m, k = len(A), len(B[0]), len(B)
    out = [[0j for _ in range(m)] for _ in range(n)]
    for i in range(n):
        for j in range(m):
            s = 0j
            for t in range(k):
                s += A[i][t] * B[t][j]
            out[i][j] = s
    return out

def dagger(A):
    return [[A[i][j].conjugate() for i in range(len(A))] for j in range(len(A[0]))]

def eye(n):
    return [[(1+0j if i == j else 0j) for j in range(n)] for i in range(n)]

def vec_basis(n, idx):
    v = [0j] * n
    v[idx] = 1+0j
    return v

def matvec(A, v):
    return [sum(A[i][j]*v[j] for j in range(len(v))) for i in range(len(A))]

def equal_mat(A, B, eps=1e-12):
    for i in range(len(A)):
        for j in range(len(A[0])):
            if abs(A[i][j] - B[i][j]) > eps:
                return False
    return True

def equal_vec(a, b, eps=1e-12):
    return all(abs(a[i] - b[i]) <= eps for i in range(len(a)))

# N)Nash: :=: not found
OMEGAD = [
    [1+0j, 0+0j],
    [0+0j,-1+0j],
]

# Cross: |a b c> -> |b c a| on 3 qubits (8-dim)
def cross_matrix():
    U = [[0j for _ in range(8)] for _ in range(8)]
    for a, b, c in product([0, 1], repeat=3):
        inp = (a << 2) | (b << 1) | c
        out = (b << 2) | (c << 1) | a
        U[out][inp] = 1+0j
    return U

CROSS = cross_matrix()

def test_omegad_unitary_and_involutory():
    I2 = eye(2)
    assert equal_mat(matmul(dagger(OMEGAD), OMEGAD), I2)
    assert equal_mat(matmul(OMEGAD, OMEGAD), I2)

def test_omegad_basis_action():
    ket0 = vec_basis(2, 0)
    ket1 = vec_basis(2, 1)
    assert equal_vec(matvec(OMEGAD, ket0), ket0)
    assert equal_vec(matvec(OMEGAD, ket1), [0j, -1+0j])

def test_cross_unitary():
    I8 = eye(8)
    assert equal_mat(matmul(dagger(CROSS), CROSS), I8)

def test_cross_order_three():
    I8 = eye(8)
    U2 = matmul(CROSS, CROSS)
    U3 = matmul(U2, CROSS)
    assert equal_mat(U3, I8)

def test_cross_basis_mapping():
    for a, b, c in product([0, 1], repeat=3):
        inp_idx = (a << 2) | (b << 1) | c
        exp_idx = (b << 2) | (c << 1) | a
        v = vec_basis(8, inp_idx)
        out = matvec(CROSS, v)
        exp = vec_basis(8, exp_idx)
        assert equal_vec(out, exp)
