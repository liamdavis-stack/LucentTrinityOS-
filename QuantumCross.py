from operators.xi_gamma import XiGamma
from operators.omega_delta import OmegaDelta
def cycle(state):
    return [XiGamma().apply(state), OmegaDelta().apply(state)]
