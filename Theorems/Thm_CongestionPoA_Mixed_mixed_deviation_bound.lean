import Mathlib
import Definitions.Def_agt_games
import Definitions.Def_CongestionPoA_Mixed_Model

namespace CongestionPoA.Mixed

/-- Christodoulou and Koutsoupias, *The Price of Anarchy of Finite Congestion Games*, STOC 2005,
Theorem 1, proof (PDF p. 3), applied to mixed profiles as in Sect. 5 (PDF p. 6): the deviation
inequality. Let the latencies be `f_e(k) = a_e·k + b_e` with `a_e, b_e ≥ 0`, let `σ` be a mixed Nash
equilibrium and `P` a pure strategy profile. Then for every player `i`,
`E[cᵢ] ≤ Σ_{e∈Pᵢ} (a_e·(E[n_e] + 1) + b_e)`.

**Formalization Note.** The paper displays the pure case with identity latencies,
`cᵢ(A) = Σ_{e∈Aᵢ} n_e(A) ≤ Σ_{e∈Pᵢ} n_e(A₋ᵢ, Pᵢ) ≤ Σ_{e∈Pᵢ} (n_e(A) + 1)`; Sect. 5 says the proof of
Theorem 1 carries over to mixed equilibria. Here the latencies are the paper's affine ones (Sect. 2),
the coefficients are explicit binders, `E[·]` is under the product distribution of `σ`, and `P` is
feasible (`Pᵢ ∈ Σᵢ`), which is what makes switching to `Pᵢ` a legal deviation. -/
theorem mixed_deviation_bound {ι E : Type*} [Fintype ι] [DecidableEq ι] [Fintype E] [DecidableEq E]
    (G : CongestionPoA.AsymSum.CongestionGame ι E) (a b : E → ℝ) (ha : ∀ e, 0 ≤ a e) (hb : ∀ e, 0 ≤ b e)
    (hlat : ∀ e k, G.latency e k = a e * k + b e)
    (σ : ∀ i, ↥(G.strategies i) → ℝ) (hσ : IsMixedNash G σ)
    (P : ι → Finset E) (hP : CongestionPoA.AsymSum.IsProfile G P) (i : ι) :
    expCost G σ i ≤ ∑ e ∈ P i, (a e * (expLoad G σ e + 1) + b e) := by sorry

end CongestionPoA.Mixed

