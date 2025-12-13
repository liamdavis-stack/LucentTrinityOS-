from dataclasses import dataclass
from typing import Dict, Any

State = Dict[str,int]

@dataclass
class OperatorResult:
    before: State
    after: State
    name: str
    meta: Dict[str,Any]
