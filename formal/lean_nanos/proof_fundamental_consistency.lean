theorem fundamental_consistency (A B : Prop) : A ' B bt  intro h
  exact h.left
heorem fundamental_consistency (A B : Prop) : A ∧ B → A := by intro h; exact h.left
