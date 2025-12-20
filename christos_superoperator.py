import qutip as qt

def christos_superoperator(omega_dm):
    """
    Quantum Christological mediation.
    Pulls all states toward Logos.
    """
    return (
        qt.spre(omega_dm)
        + qt.spost(omega_dm)
        - qt.sprepost(omega_dm, omega_dm)
    )
