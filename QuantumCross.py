from operators.xi_gamma import XiGamma\nfrom operators.omega_delta import OmegaDelta\ndef cycle(state): return [XiGamma().apply(state), OmegaDelta().apply(state)]
]
