# Initialize engine and circuit
engine = LTOS_M24_Engine_Validated(
    octads=golay_octads(),
    dodecads=golay_dodecads(),
    perms_seed=perms_seed
)

circuit = QuantumCircuitM24Gates(engine)

# Sender qubit (Octad0)
octad0 = support(golay_octads()[0])
# Receiver qubit (Octad1)
octad1 = support(golay_octads()[1])

# Initialize sender qubit in superposition |+> = H|0>
 = np.zeros(24, dtype=np.complex128)
[octad0.pop()] = 1.0  # prepare |0> state in Octad0
circuit.initialize_state()

# Step 1: Entangle Octad0 and Octad1
H0 = hadamard_gate(octad0)
circuit.apply_gate(H0, name="Hadamard_Octad0")
CNOT_01 = cnot_gate(octad0, octad1)
circuit.apply_gate(CNOT_01, name="CNOT_Octad0_to_Octad1")

# Step 2: Measure sender qubit (Octad0)
prob0 = circuit.measure(octad0, name="Measure_Octad0")
print(f"Measurement probability (Octad0): {prob0:.6f}")

# Step 3: Conditional correction (phase gate) on Octad1
# For simplicity, apply phase unconditionally (simulates classical feedforward)
phase_correction = phase_gate(octad1, np.pi)
circuit.apply_gate(phase_correction, name="Phase_Correction_Octad1")

# Step 4: Verify receiver state
prob1 = circuit.measure(octad1, name="Measure_Octad1")
print(f"Measurement probability (Octad1): {prob1:.6f}")

print("Teleportation circuit history:", circuit.history)
