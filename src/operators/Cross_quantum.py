"""
Legacy import shim for CI/tests.

Old: from src.operators.Cross_quantum import Cross_quantum
New canonical: src.axiom_engine.operators.cross
"""

from src.axiom_engine.operators.cross import cross as Cross_quantum
from src.axiom_engine.operators.cross import cross_inverse as Cross_inverse_quantum

__all__ = ["Cross_quantum", "Cross_inverse_quantum"]
