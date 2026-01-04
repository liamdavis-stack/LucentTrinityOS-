def total_conservation(before, after, meta):
    return sum(before.values()) == sum(after.values())
