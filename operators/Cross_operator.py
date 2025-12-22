# ==========================================
# LucentTrinityOS - Operator Canon Artifact
# Operator: b# Decomposition: 8 + 8 + 8 (Steiner S(5,8,24) octads)
# Encoding: M24-native block permutation
# ==========================================
import numpy as np

OPERATOR_NAME = "Cross"
OPERATOR_DIM = 24

def get_Cross_operator():
    """
    b    Partition R^24 into three 8-dimensional Steiner octads:
        A = coords 0..7
        B = coords 8..15
        C = coords 16..23

    Action:
        (A, B, C) b
& (C, B, A)

    This is the canonical 'crossing' permutation:
    - Front and back octads swap.
    - Middle octad remains fixed.
    - Orthogonal, norm-preserving, and M24-compatible.
    """
    perm = np.array(
        list(range(16,24)) +   # C b
        list(range(8,16))  +   # B stays in middle
        list(range(0,8))       # A b
    )
    Cross = np.eye(24)[perm]
    return Cross


def get_operator_metadata():
    """
    Return a minimal metadata dictionary for audit and registry.
    """
    return {
        "name": OPERATOR_NAME,
        "dimension": OPERATOR_DIM,
        "decomposition": "24 = 8 + 8 + 8 (Steiner octads)",
        "action": "(A, B, C) b
& (C, B, A)",
        "native_encoding": "Steiner S(5,8,24) block permutation",
        "orthogonal": True,
    }


if __name__ == "__main__":
    # Minimal self-check for manual/CI use
    Cross = get_Cross_operator()
    # Check shape
    assert Cross.shape == (24, 24)
    # Check orthogonality: Cross^T Cross = I exactly
    approx_I = Cross.T @ Cross
    err = np.linalg.norm(approx_I - np.eye(24))
    print(f"[Cross] shape={Cross.shape}, orthogonality_error={err:.3e}")

