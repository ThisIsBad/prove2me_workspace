import Mathlib
import Definitions.Def_NSWApxHard_Reduction_Instance

namespace NSWApxHard.Reduction

/-- Completeness (Lee, p. 2): if the 3-regular graph `G` has a vertex cover `C` of size `k`, the
reduced instance with `k` vertex items has an allocation of Nash social welfare
`(1 + α)^{(3k - 1.5N)/(2.5N)}`, i.e. `(1 + α)^{β/2.5}` with `β N = 3k - 1.5N`. -/
theorem completeness {N : ℕ} (G : SimpleGraph (Fin N)) [DecidableRel G.Adj] (k : ℕ) (α : ℝ)
    (hG : IsCubic G) (hα₁ : 1 / 3 < α) (hα₂ : α < 1 / 2)
    (C : Finset (Fin N)) (hC : G.IsVertexCover ↑C) (hCk : C.card = k) :
    ∃ x : Item G k → Agent G,
      nsw (redUtil G k α) x = (1 + α) ^ ((3 * (k : ℝ) - 3 * N / 2) / (5 * N / 2)) := by sorry

end NSWApxHard.Reduction

