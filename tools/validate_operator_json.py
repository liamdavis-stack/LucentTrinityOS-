import json, sys, re

path = sys.argv[1] if len(sys.argv) > 1 else None
if not path:
    print("usage: python3 tools/validate_operator_json.py <path.json>")
    sys.exit(2)

with open(path, "r", encoding="utf-8") as f:
    d = json.load(f)

required = ["id","name","symbol","version","layer","category","status"]
missing = [k for k in required if k not in d]
if missing:
    print("FAIL missing keys:", missing)
    sys.exit(1)

# Optional LTOS fields (recommended)
recommended = ["kind","dispatch_name","entrypoint"]
rec_missing = [k for k in recommended if k not in d]
if rec_missing:
    print("WARN missing recommended keys:", rec_missing)

ep = d.get("entrypoint")
if ep is not None:
    # very light validation: module.path:callable
    if ":" not in ep or ep.startswith(":") or ep.endswith(":"):
        print("FAIL entrypoint format should look like module.path:callable")
        sys.exit(1)

print("OK operator json:", d["id"], d["name"], d["symbol"])
