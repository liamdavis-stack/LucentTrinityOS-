class OperatorValidator:
    def __init__(self,axioms): self.axioms=axioms
    def validate(self,result): 
        return all(ax(result.before,result.after,result.meta) for ax in self.axioms)
