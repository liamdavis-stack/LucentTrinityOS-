def compose(*ops):\n    def f(state):\n        s = state\n        for op in ops: s = op.apply(s)\n        return s\n    return f
