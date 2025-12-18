class Operator:\n    def name(self): return self.__class__.__name__\n    def apply(self, state): raise NotImplementedError
