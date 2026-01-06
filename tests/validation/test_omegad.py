



import pytest
try:
    import numpy as np
    from qiskit.quantum_info import Operator
except Exception as e:
    pytest.skip(f"Skipping NumPy/Qiskit tests in this environment (iOS/iSH): {e}", allow_module_level=True)
import numpy as np
from qiskit.quantum_info import Operator
from src.axiom_engine.operators.omega_delta import omega_delta as OmegaD_quantum

def test_omegad_is_unitary():
    U = Operator(OmegaD_quantum()).data
    I = np.eye(2, dtype=complex)
    assert np.allclose(U.conj().T @ U, I)

def test_omegad_is_involutory():
    U = Operator(OmegaD_quantum()).data
    I = np.eye(2, dtype=complex)
    assert np.allclose(U @ U, I)

def test_omegad_action_on_basis():
    U = Operator(OmegaD_quantum()).data
    ket0 = np.array([1, 0], dtype=complex)
    ket1 = np.array([0, 1], dtype=complex)
    assert np.allclose(U @ ket0, ket0)
    assert np.allclose(U @ ket1, -ket1)
