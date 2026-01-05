from dataclasses import dataclass
from typing import Dict, Any

State = Dict[str,int]

@dataclass
class OperatorResult:
    before: State
    after: State
    name: str
    meta: Dict[str,Any]

# --- operator entrypoint (required by TrinityKernel) -------------------------
def base(state: State, **meta) -> OperatorResult:
    """Identity/base operator. Returns state unchanged with audit metadata."""
    before = dict(state)
    after  = dict(state)
    return OperatorResult(before=before, after=after, name="base", meta=dict(meta))

