import Mathlib
import Definitions.Def_VapnikChervonenkis_Shared_Phi
import Definitions.Def_VapnikChervonenkis_Shared_index
import Definitions.Def_VapnikChervonenkis_Shared_growthFunction

namespace VapnikChervonenkis.GrowthFunction

/-- **Lemma 1** of Vapnik and Chervonenkis (1971), p. 266: if for some sample `x_1, ···, x_i` of
size `i` and some number `n` with `1 ≤ n ≤ i` one has `Δ^S(x_1, ···, x_i) ≥ Φ(n, i)`, then there is
a subsample `x_{i_1}, ···, x_{i_n}` of this sample (positions `i_1 < ··· < i_n`) with
`Δ^S(x_{i_1}, ···, x_{i_n}) = 2^n`. -/
theorem lemma1_shattered_subsample {X : Type*} (S : Set (Set X)) (i n : ℕ) (x : Fin i → X)
    (hn1 : 1 ≤ n) (hni : n ≤ i) (hΔ : Shared.Phi n i ≤ Shared.index S x) :
    ∃ e : Fin n → Fin i, StrictMono e ∧ Shared.index S (x ∘ e) = 2 ^ n := by sorry

end VapnikChervonenkis.GrowthFunction

