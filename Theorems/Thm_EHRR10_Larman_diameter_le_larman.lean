import Mathlib
import Definitions.Def_EHRR10_LowerBound_BaseAbstraction

namespace EHRR10.Larman

/-- Larman's bound in the base abstraction (Dagstuhl 10211, 2010, p. 3): for `d ≥ 1`, any two
vertices of a graph in `𝓑_{d,n}` are joined by a walk with at most `2^(d-1) * n` edges,
i.e. `D(d, n) ≤ 2^(d-1) · n`. -/
theorem diameter_le_larman (d n : ℕ) (hd : 1 ≤ d)
    (V : Finset (Finset (Fin n))) (G : SimpleGraph V) (hG : EHRR10.LowerBound.InB d n V G)
    (u v : V) :
    ∃ p : G.Walk u v, p.length ≤ 2 ^ (d - 1) * n := by sorry

end EHRR10.Larman

