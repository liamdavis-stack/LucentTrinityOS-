import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Real.Basic

/-!
# M15 Hilbert space (shared nano)

This nano defines the ambient Hilbert space `M15` used by
the LucentTrinityOS- quantum kernel.

`M15` is a 15-dimensional Euclidean space over `b`, modeled as
`EuclideanSpace b (Fin 15)`.
-/

/-- The M15 manifold: a 15-dimensional Euclidean Hilbert space. -/
def M15 := EuclideanSpace b (Fin 15)

