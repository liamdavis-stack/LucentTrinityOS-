from copy import deepcopy
from .base import OperatorResult

def apply_omega_delta(state, gain=0):
    before = deepcopy(state)
    after = deepcopy(state)
    for k in after: after[k]+=gain
    meta={"symbol":"Ωᴰ","gain":gain,"op":"ghz_scaffold"}
    return OperatorResult(before,after,"OmegaDelta",meta)

# Kernel entrypoint wrapper (iSH-safe)
def omega_delta(state, *args, **kwargs):
    return apply_omega_delta(state, *args, **kwargs)


# ----------------------------
# CI contract: OmegaD_quantum
# ----------------------------
def OmegaD_quantum():
    """
    CI/test contract (validation/test_omegad.py):

    - Unitary
    - Involutory: U @ U == I
    - Acts as: |0> -> |0>, |1> -> -|1>

    This is the Pauli-Z gate: diag(1, -1).
    Returned as a simple Python nested list (qiskit Operator accepts array-like).
    """
    return [
        [1+0j, 0+0j],
        [0+0j, -1+0j],
    ]


__all__ = list(globals().get("__all__", [])) + ["OmegaD_quantum"]
