from qiskit import QuantumCircuit

def Cross_quantum():
    """
    Quantum analogue of the b        (q0, q1, q2) -> (q2, q0, q1)
    This is the Path A reduction of the 24D Steiner octad crossing.
    """
    qc = QuantumCircuit(3)

    # Perform the 3-cycle using SWAP gates
    qc.swap(0, 2)   # (q0, q1, q2) -> (q2, q1, q0)
    qc.swap(1, 2)   # (q2, q1, q0) -> (q2, q0, q1)

    return qc

