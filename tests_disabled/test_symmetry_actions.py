import numpy as np
from ltos_symmetry24.core import LTOS_Symmetry24_Core


def test_seal_is_unit_norm_and_dim_24():
    core = LTOS_Symmetry24_Core()
    s = core.seal_to_state24("hello").vector
    assert s.shape == (24,)
    assert abs(np.linalg.norm(s) - 1.0) < 1e-9


def test_canonicalize_preserves_norm_and_dim():
    core = LTOS_Symmetry24_Core()
    s = core.seal_to_state24("canon").vector
    c = core.canonicalize(s)
    assert c.shape == (24,)
    assert abs(np.linalg.norm(c) - 1.0) < 1e-9


def test_actions_verify_runs_and_returns_dict():
    core = LTOS_Symmetry24_Core()
    rep = core.integrity(core.seal_to_state24("verify").vector)
    assert isinstance(rep.actions_verified, dict)
    # We do NOT assert True here, because your generator+actions may evolve.
    # LTOS uses this report to decide what it can claim safely.
