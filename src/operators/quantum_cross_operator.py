from qiskit import QuantumCircuit
from qiskit.circuit.library import RXGate, RZGate

def quantum_cross_operator(theta):
    """
    Quantum Cross Operator (Path A)
    A 2-qubit cross-axis mixer using native IBM gates.
    """
    qc = QuantumCircuit(2)

    # Step 1: Entangle
    qc.cx(0, 1)

    # Step 2: Cross rotations
    qc.rx(theta, 0)
    qc.rz(theta, 1)

    # Step 3: Disentangle
    qc.cx(0, 1)

    return qc

