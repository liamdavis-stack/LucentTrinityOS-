from qiskit import QuantumCircuit\n\n# Placeholder for Shor's factoring routine\nqc = QuantumCircuit(4)\nqc.h([0,1,2])\nqc.cx(0,3)\nqc.cx(1,3)\nqc.cx(2,3)\nqc.measure_all()\nprint(qc)
