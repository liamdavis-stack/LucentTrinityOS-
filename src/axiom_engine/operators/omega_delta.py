from copy import deepcopy
from operators.base import OperatorResult

def apply_omega_delta(state, gain=0):
    before = deepcopy(state)
    after = deepcopy(state)
    for k in after: after[k]+=gain
    meta={"symbol":"Ωᴰ","gain":gain,"op":"ghz_scaffold"}
    return OperatorResult(before,after,"OmegaDelta",meta)
