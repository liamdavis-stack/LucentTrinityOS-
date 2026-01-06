import numpy as np
from ltos_symmetry24.golay import default_golay_like_generator, generate_code_from_generator


def test_code_has_expected_size_and_shape():
    code = generate_code_from_generator(default_golay_like_generator())
    assert code.codewords.shape == (2 ** code.k, 24)
    assert code.k == 12
    assert code.n == 24


def test_code_contains_zero_and_is_closed_under_xor():
    code = generate_code_from_generator(default_golay_like_generator())
    zero = np.zeros(24, dtype=int)
    assert code.contains(zero)

    # Random closure checks (fast and CI-safe)
    rng = np.random.default_rng(0)
    for _ in range(100):
        a = code.codewords[rng.integers(0, len(code.codewords))]
        b = code.codewords[rng.integers(0, len(code.codewords))]
        c = (a ^ b)  # XOR in GF(2)
        assert code.contains(c)
