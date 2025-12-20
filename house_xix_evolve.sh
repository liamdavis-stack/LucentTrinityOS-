#!/bin/sh
# ==========================================
# House XIX Evolution Script b
ash: ASCII: not found
# Automates: Lean4 -> GravityAuditor -> Git -> Push
# ==========================================

echo "Starting House XIX evolution sequence..."

# 1) Run Lean4 simulation to output JSON
echo "Generating Lean4 results..."
lean --run Houses/House_XIX/black_hole_thermodynamics.lean || { echo "Lean4 simulation failed"; exit 1; }

# 2) Run Python GravityAuditor
echo "Running GravityAuditor..."
python3 Houses/House_XIX/black_hole_sim_bridge.py || { echo "GravityAuditor execution failed"; exit 1; }

# 3) Stage Lean JSON results and audit log
echo "Staging files for Git..."
git add Houses/House_XIX/house_xix_results.json Houses/House_XIX/house_xix_audit.json || { echo "Git add failed"; exit 1; }

# 4) Commit changes
COMMIT_MSG="House XIX: Auto-update audit from Lean4 simulation"
git commit -m "$COMMIT_MSG" || echo "Nothing to commit; working tree clean"

# 5) Push to remote
echo "Pushing to GitHub..."
git push origin main || { echo "Git push failed"; exit 1; }

echo "House XIX evolution complete!"
