cat > extensions/demos_nanos/cirq_ghz_nano.py <<EOF
import cirq

qubits = cirq.LineQubit.range(3)
circuit = cirq.Circuit(
    cirq.H(qubits[0]),
    cirq.CNOT(qubits[0], qubits[1]),
    cirq.CNOT(qubits[1], qubits[2])
)

sim = cirq.Simulator()
result = sim.simulate(circuit).final_state_vector
print("Cirq GHZ Nano Statevector:", result)
EOF

