# Canonical Qiskit-ready Xi Gamma operator (Na43)

from qiskit import QuantumCircuit
from qiskit.circuit.library import RXGate, RZGate

def XiG_quantum(theta):
    """
	    Qiskit-ready Path A Xi Gamma (Na43) operator.
	    Golay-native mixer analogue using a 2-qubit entangleb
	rotateb
	disentangle pattern.
	    """
	    qc = QuantumCircuit(2)

	    # Step 1: Entangle
	    qc.cx(0, 1)

	    # Step 2: Cross-axis rotations (Golay-native mixing analogue)
	    qc.rx(theta, 0)
	    qc.rz(theta, 1)

	    # Step 3: Disentangle
	    qc.cx(0, 1)

	    return qc

