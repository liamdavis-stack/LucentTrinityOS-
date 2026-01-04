"""
Cross Operator (LucentTrinityOS)

Formalization target: academically legible + mechanically checkable.

Hilbert space: H = (C^2)^{b

Definition (basis action):
    Cross |a b c> = |b c a>.

Interpretation:
    Cross is the left cyclic shift (a 3-cycle) of the three qubit registers.

Key properties:
    1) Unitary:
        Cross is a permutation unitary in the computational basis, so Crossb
  Cross = I.
    2) Order 3:
        Cross^2 |a b c> = |c a b>
        Cross^3 |a b c> = |a b c>
        Therefore Cross^3 = I.
    3) Inverse:
        Cross^{-1} = Cross^2.

Circuit construction:
    Cross is implemented as SWAP(0,1) followed by SWAP(1,2),
    which realizes |a b c> -> |b c a>.
"""

from __future__ import annotations

from qiskit import QuantumCircuit


def Cross_quantum() -> QuantumCircuit:
    """
    Construct the Cross operator as a Qiskit circuit.

    Returns:
        QuantumCircuit: 3-qubit circuit implementing Cross |a b c> = |b c a>.

    Construction proof sketch:
        Start with |a b c>.
        After SWAP(0,1): |b a c>.
        After SWAP(1,2): |b c a>.
        Hence the circuit equals the defined permutation unitary.

    Formal claims (validated in separate tests):
        - Unitary
        - Order 3 (Cross^3 = I)
        - Inverse equals Cross^2
    """
    qc = QuantumCircuit(3, name="Cross")
    qc.swap(0, 1)
    qc.swap(1, 2)
    return qc


def Cross_inverse_quantum() -> QuantumCircuit:
    """
    Construct Cross^{-1} as a Qiskit circuit.

    Since Cross^{-1} = Cross^2 and Cross^3 = I, we can implement Cross^{-1}
    as the right cyclic shift:

        Cross^{-1} |a b c> = |c a b>.

    Circuit construction:
        SWAP(1,2) then SWAP(0,1) maps |a b c> -> |a c b> -> |c a b>.
    """
    qc = QuantumCircuit(3, name="Cross^{-1}")
    qc.swap(1, 2)
    qc.swap(0, 1)
    return qc
