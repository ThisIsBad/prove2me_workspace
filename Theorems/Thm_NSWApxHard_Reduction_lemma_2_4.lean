import Mathlib
import Definitions.Def_NSWApxHard_Reduction_Instance

namespace NSWApxHard.Reduction

/-- Lemma 2.4 (Lee, p. 4): if every vertex cover of the 3-regular graph `G` has at least `K'`
vertices (the paper's `c_max N`) and there are `k < N` vertex items (the paper's `c_min N`), then
every allocation of the reduced instance has Nash social welfare at most
`(2(1+α)/3)^{γ/2.5} (1 + α)^{β/2.5}`, where `γ N = (K' - k)/3` and `β N = 3k - 1.5N`. -/
theorem lemma_2_4 {N : ℕ} (G : SimpleGraph (Fin N)) [DecidableRel G.Adj] (k : ℕ) (α K' : ℝ)
    (hG : IsCubic G) (hα₁ : 1 / 3 < α) (hα₂ : α < 1 / 2) (hk : k < N)
    (hK' : ∀ C : Finset (Fin N), G.IsVertexCover ↑C → K' ≤ (C.card : ℝ))
    (x : Item G k → Agent G) :
    nsw (redUtil G k α) x ≤
      (2 * (1 + α) / 3) ^ (((K' - k) / 3) / (5 * N / 2)) *
        (1 + α) ^ ((3 * (k : ℝ) - 3 * N / 2) / (5 * N / 2)) := by sorry

end NSWApxHard.Reduction

