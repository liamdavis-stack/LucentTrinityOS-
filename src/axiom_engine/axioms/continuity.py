def identity_continuity(before, after, meta):
    keys = set(before.keys()) | set(after.keys())
    return all(after.get(k,0) >= 0 for k in keys)
