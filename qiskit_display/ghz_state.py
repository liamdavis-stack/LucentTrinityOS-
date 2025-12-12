from qiskit import QuantumCircuit\n\nqc = QuantumCircuit(3)\nqc.h(0)\nqc.cx(0,1)\nqc.cx(0,2)\nprint(qc)
