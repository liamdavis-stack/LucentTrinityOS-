from axioms.continuity import continuity
from axioms.conservation import conservation
def certify(state): return [continuity(state), conservation(state)]
