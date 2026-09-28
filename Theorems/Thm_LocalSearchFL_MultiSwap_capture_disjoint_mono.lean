import Mathlib
import Definitions.Def_LocalSearchFL_MultiSwap_capture

namespace LocalSearchFL.MultiSwap

/-- §3.4, p. 551: for `X, Y ⊆ S`, if `X` and `Y` are disjoint then `capture(X)` and `capture(Y)`
are disjoint, and if `X ⊆ Y` then `capture(X) ⊆ capture(Y)`. -/
theorem capture_disjoint_mono {Cl Fa : Type} [Fintype Cl] [DecidableEq Cl] [DecidableEq Fa]
    (σS σO : Cl → Fa) (S O X Y : Finset Fa) (hX : X ⊆ S) (hY : Y ⊆ S) :
    (Disjoint X Y → Disjoint (capture σS σO O X) (capture σS σO O Y)) ∧
      (X ⊆ Y → capture σS σO O X ⊆ capture σS σO O Y) := by sorry

end LocalSearchFL.MultiSwap
