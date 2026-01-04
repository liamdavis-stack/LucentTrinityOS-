from qiskit import QuantumCircuit

def OmegaD_quantum():
    qc = QuantumCircuit(1, name="OmegaD")
    qc.z(0)
    return qc
