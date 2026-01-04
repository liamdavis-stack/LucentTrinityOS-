from copy import deepcopy
from operators.base import OperatorResult

def apply_xi_gamma(state,bias=("000",-16),rebalance=("111",+16)):
    before=deepcopy(state); after=deepcopy(state)
    k1,d1=bias; k2,d2=rebalance
    after[k1]=max(0,after.get(k1,0)+d1)
    after[k2]=max(0,after.get(k2,0)+d2)
    meta={"symbol":"Ξᴳ","bias":bias,"rebalance":rebalance,"op":"6d_override"}
    return OperatorResult(before,after,"XiGamma",meta)
