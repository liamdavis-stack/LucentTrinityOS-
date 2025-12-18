def compose(*ops):
    def f(state):
        s = state
        for op in ops: s = op.apply(s)
        return s
    return f
