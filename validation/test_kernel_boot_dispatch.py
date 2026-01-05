def test_kernel_boots_and_dispatch_resolves_known_ops():
    from src.axiom_engine.dispatch import dispatch_operator

    # Boot criteria: module imports and registry resolves known operators.
    dispatch_operator("cross")
    dispatch_operator("cross_inverse")
    dispatch_operator("omega_delta")
    dispatch_operator("theta_entanglement_exchange")
