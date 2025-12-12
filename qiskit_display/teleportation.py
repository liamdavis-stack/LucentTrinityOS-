from qiskit import QuantumCircuit\n\nqc = QuantumCircuit(3)\nqc.h(1)\nqc.cx(1,2)\nqc.cx(0,1)\nqc.h(0)\nqc.measure_all()\nprint(qc)
