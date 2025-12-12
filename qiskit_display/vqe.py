from qiskit import QuantumCircuit\n\n# Simple VQE ansatz circuit\nqc = QuantumCircuit(2)\nqc.h(0)\nqc.cx(0,1)\nqc.rx(0.5,0)\nqc.ry(0.5,1)\nprint(qc)
