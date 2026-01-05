# src/axiom_engine/operators/cross.py

def cross():
    """
    Canonical Cross quantum operator.
    Involutory diagonal operator.
    """
    return [
        [1+0j, 0+0j],
        [0+0j, -1+0j],
    ]

def cross_inverse():
    return cross()

__all__ = ["cross", "cross_inverse"]
