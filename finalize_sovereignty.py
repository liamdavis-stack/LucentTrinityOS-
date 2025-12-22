import numpy as np
from CVPSolver_Fast import CVPSolver_Fast
from LTOS_Compiled_Core_Enhanced import LTOS_Compiled_Core_Enhanced

def finalize_sovereignty(core, content):
    solver = CVPSolver_Fast(core)

    raw_state = core.map_to_manifold_uniform(content)
    sovereign_state = solver.decode(raw_state)
    transformed = core.apply_m24_unitary(sovereign_state, gen_idx=0)

    return sovereign_state, transformed

if __name__ == "__main__":
    core = LTOS_Compiled_Core_Enhanced()
    state, verified = finalize_sovereignty(core, "Final Sovereign Initialization")
    print(f"Final State Fidelity: {np.vdot(state, verified).real:.6f}")

