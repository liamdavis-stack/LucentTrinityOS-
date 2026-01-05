"""
Legacy import shim (iSH-safe).
"""
from src.axiom_engine.operators.cross import cross as Cross_quantum
from src.axiom_engine.operators.cross import cross_inverse as Cross_inverse_quantum

__all__ = ["Cross_quantum", "Cross_inverse_quantum"]
