"""
Legacy import shim for CI/tests.

Old: from src.operators.OmegaD_quantum import OmegaD_quantum
New canonical: src.axiom_engine.operators.omega_delta
"""

from src.axiom_engine.operators.omega_delta import omega_delta as OmegaD_quantum

__all__ = ["OmegaD_quantum"]
