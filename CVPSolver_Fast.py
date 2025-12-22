import numpy as np

class CVPSolver_Fast:
    def __init__(self, core_enhanced):
        self.core = core_enhanced
        self.basis = core_enhanced.leech_basis

    def decode(self, target_vector):
        y = target_vector.real * np.sqrt(8)
        f = 2 * np.round(y / 2)

        best_dist = np.inf
        best_vec = None

        for codeword in self.core.golay_code:
            candidate = f + codeword
            dist = np.linalg.norm(y - candidate)
            if dist < best_dist:
                best_dist = dist
                best_vec = candidate

        return (best_vec / np.linalg.norm(best_vec)).astype(complex)

