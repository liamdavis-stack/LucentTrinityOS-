"""
Legacy compatibility shim for CI/tests.

Canonical cross operator no longer exists as a standalone implementation.
This stub exists to satisfy historical imports.
"""

def Cross_quantum(*args, **kwargs):
    raise NotImplementedError(
        "Cross_quantum has been deprecated. "
        "Use canonical axiom_engine operators instead."
    )

def Cross_inverse_quantum(*args, **kwargs):
    raise NotImplementedError(
        "Cross_inverse_quantum has been deprecated."
    )

__all__ = ["Cross_quantum", "Cross_inverse_quantum"]
