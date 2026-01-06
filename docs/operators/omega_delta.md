# ΩΔ — Omega Delta (Sealing Operator)

## (A) Mathematical / Computer Science Contract (PRIMARY)

**Definition:** ΩΔ is the single-qubit Pauli-Z operator.

\[
ΩΔ \equiv Z =
\begin{bmatrix}
1 & 0 \\
0 & -1
\end{bmatrix}
\]

**Invariants (provable, testable):**
- **Unitary:** \(Z^\dagger Z = I\)
- **Involutory:** \(Z^2 = I\)
- **Basis action:** \(Z|0\rangle = |0\rangle,\; Z|1\rangle = -|1\rangle\)
- **Eigenvalues:** \(\{+1,-1\}\) with eigenbasis \(\{|0\rangle,|1\rangle\}\)

**Implementation contract (LucentTrinityOS):**
- `omega_delta()` returns a pure-Python `2x2` complex list-of-lists.
- `omega_delta(state_dict)` returns a shallow-copied dict tagged with `state["op"] = "ΩΔ"` (legacy pipeline metadata).

**Canonical source:**
- `src/axiom_engine/operators/omega_delta.py`

**Tests:**
- `tests/validation/test_omegad.py`

## (B) Symbolic / Theological Contract (SECONDARY, METADATA)

Within LucentTrinityOS, ΩΔ is the **“Sealing”** operator.

Symbolically, sealing denotes closure/marking/covenantal boundary applied to a state transition.

**Constraints:**
- This operator does **not** assert metaphysical proof.
- Mathematical correctness is independent of symbolic interpretation.
- The symbolic layer exists as metadata only and does not alter the (A) contract.
