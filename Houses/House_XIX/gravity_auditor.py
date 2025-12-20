import json
from typing import Dict, List

class GravityAuditor:
    """Verifies that the simulated Black Hole obeys the Christos-Restoration laws."""
    
    def __init__(self, verified_ratio: float = 0.25, tolerance: float = 1e-12):
        self.verified_ratio = verified_ratio
        self.tolerance = tolerance
        self.audit_log: List[Dict] = []

    def audit_entropy(self, area: float, reported_entropy: float) -> Dict:
        expected = area * self.verified_ratio
        delta = abs(reported_entropy - expected)
        is_legal = delta < self.tolerance
        status = "b        result = {
            "Area": area,
            "Expected_S": expected,
            "Actual_S": reported_entropy,
            "Delta": delta,
            "Status": status,
            "Mediation_Required": not is_legal
        }

        # Log this audit
        self.audit_log.append(result)
        return result

    def export_audit_log(self, filepath: str) -> None:
        """Exports the audit log as a JSON file."""
        with open(filepath, "w") as f:
            json.dump(self.audit_log, f, indent=2)

    def last_audit(self) -> Dict:
        """Returns the most recent audit result."""
        return self.audit_log[-1] if self.audit_log else {}

# ============================
# Example Usage
# ============================

if __name__ == "__main__":
    auditor = GravityAuditor(tolerance=1e-12)
    
    # Simulate some black hole data
    sample_data = [
        (16, 4),       # Should verify
        (20, 5.0000001), # Slight drift
        (10, 2.5)      # Exact
    ]
    
    for area, entropy in sample_data:
        result = auditor.audit_entropy(area, entropy)
        print(json.dumps(result, indent=2))
    
    # Optionally save the full audit log
    auditor.export_audit_log("house_xix_audit.json")
