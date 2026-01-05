"""
Canonical operator dispatch for LucentTrinityOS.

Goal:
- Provide a stable API CI can validate:
    from src.axiom_engine.dispatch import dispatch_operator
    op = dispatch_operator("cross")  # returns a callable operator
"""

from __future__ import annotations

from typing import Callable, Dict, Any

# Import canonical operator callables from axiom_engine
from src.axiom_engine.operators.cross import cross, cross_inverse
from src.axiom_engine.operators.omega_delta import omega_delta
from src.axiom_engine.operators.theta_entanglement_exchange import theta_entanglement_exchange


_REGISTRY: Dict[str, Callable[..., Any]] = {
    "cross": cross,
    "cross_inverse": cross_inverse,
    "omega_delta": omega_delta,
    "theta_entanglement_exchange": theta_entanglement_exchange,
}


def dispatch_operator(name: str) -> Callable[..., Any]:
    """
    Return the operator callable registered under `name`.

    Raises:
        KeyError if the operator name is unknown.
    """
    try:
        return _REGISTRY[name]
    except KeyError as e:
        known = ", ".join(sorted(_REGISTRY))
        raise KeyError(f"Unknown operator '{name}'. Known: {known}") from e
