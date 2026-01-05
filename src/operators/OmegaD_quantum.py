"""
Legacy import shim for CI/tests (iSH-safe: NO numpy/qiskit).

Old: from src.operators.OmegaD_quantum import OmegaD_quantum
New canonical: src.axiom_engine.operators.omega_delta
"""
from src.axiom_engine.operators.omega_delta import OmegaD_quantum

__all__ = ["OmegaD_quantum"]
