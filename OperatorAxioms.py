from axioms.continuity import continuity\nfrom axioms.conservation import conservation\ndef certify(state): return [continuity(state), conservation(state)]
