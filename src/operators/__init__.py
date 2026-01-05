"""
Legacy compatibility shim.

Old tests imported:
    from src.operators.Cross_quantum import Cross_quantum, Cross_inverse_quantum
    from src.operators.OmegaD_quantum import OmegaD_quantum

We keep these wrappers so older CI/jobs don't break.
"""
