# ==========================================
# LucentTrinityOS - Operator Canon Artifact
# Operator: N
# a43 (XiG) - Construction A Mixer 
# Dimension: 24 Decomposition: 12 + 12 (Z^12 
# b Code^12)
# Encoding: Golay / Construction A native
# ==========================================
import numpy as np

OPERATOR_NAME = "XiG"
OPERATOR_DIM = 24

def get_XiG_operator():
    """
    Na43 (XiG) - Construction A / Golay-native mixer on R^24.

    Decomposition: R^24 b R^12 b
 R^12
        First  12 coords: "integer" / base lattice sector
        Second 12 coords: "code" / Golay sector

    Action:
        (x, y) b
& ( (x + y)/2, (x - y)/2 )

    This is the canonical B1 mixing between the two 12D halves.
    It is orthogonal, preserves norms, and is native to the
    Construction A / Leech lattice viewpoint.
    """
    I12 = np.eye(12)
    XiG = (1.0 / np.sqrt(2.0)) * np.block([
        [ I12,  I12],
        [ I12, -I12]
    ])
    return XiG


def get_operator_metadata():
    """
    Return a minimal metadata dictionary for audit and registry.
    """
    return {
        "name": OPERATOR_NAME,
        "dimension": OPERATOR_DIM,
        "decomposition": "24 = 12 + 12 (Construction A split)",
        "action": "(x, y) b
& ((x + y)/2, (x - y)/2)",
        "native_encoding": "Golay-aligned, Construction A mixer",
        "orthogonal": True,
    }


if __name__ == "__main__":
    # Minimal self-check for manual/CI use
    XiG = get_XiG_operator()
    # Check shape
    assert XiG.shape == (24, 24)
    # Check basic orthogonality: XiG^T XiG b I
    approx_I = XiG.T @ XiG
    err = np.linalg.norm(approx_I - np.eye(24))
    print(f"[XiG] shape={XiG.shape}, orthogonality_error={err:.3e}")

