from qiskit import QuantumCircuit\n\nqc = QuantumCircuit(2)\nqc.h([0,1])\nqc.cz(0,1)\nqc.h([0,1])\nprint(qc)
