from qiskit import QuantumCircuit

def OmegaD_quantum():
    """
    Quantum analogue of the OmegaD operator (Path A).
    Implements a 1-qubit phase flip using a Z gate.
    """
    qc = QuantumCircuit(1)
    qc.z(0)
    return qc

