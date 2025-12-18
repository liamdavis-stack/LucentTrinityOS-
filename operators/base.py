class Operator:
    def name(self): return self.__class__.__name__
    def apply(self, state): raise NotImplementedError
