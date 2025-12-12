from qiskit import QuantumCircuit\n\nqc = QuantumCircuit(3)\nqc.h(0)\nqc.cp(3.14159/2,1,0)\nqc.h(1)\nqc.cp(3.14159/4,2,1)\nqc.h(2)\nprint(qc)
