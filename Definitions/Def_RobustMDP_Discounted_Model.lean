import Mathlib

namespace RobustMDP.Discounted

/-- A discounted infinite-horizon Markov decision process with rectangular uncertainty on its
transition rows (Nilim–El Ghaoui 2005, §2.1–2.2 pp. 781–782, §3 p. 782, §4 p. 785).
States are `Fin n` and `A` is the (state-independent) action set.

* `cost i a` is the constant cost `c(i, a)`, nonnegative and finite; the stage-`t` cost is
  `c_t(i, a) = ν^t c(i, a)` and the terminal cost is zero;
* `discount` is the discount factor `ν ∈ [0, 1)` (the range printed in Theorem 3);
* `rows a i` is the set `𝒫_i^a ⊆ Δ_n` of possible next-state distributions from state `i` under
  action `a`. The rectangular uncertainty property `𝒫^a = 𝒫_1^a × ⋯ × 𝒫_n^a` is built in: nature
  chooses each row independently from its own set. Only inclusion in the simplex is assumed (no
  convexity, no closedness); nonemptiness is implicit in the paper and made explicit here. -/
structure Model (n : ℕ) (A : Type) where
  cost : Fin n → A → ℝ
  discount : ℝ
  rows : A → Fin n → Set (Fin n → ℝ)
  cost_nonneg : ∀ i a, 0 ≤ cost i a
  discount_nonneg : 0 ≤ discount
  discount_lt_one : discount < 1
  rows_subset_simplex : ∀ a i, rows a i ⊆ stdSimplex ℝ (Fin n)
  rows_nonempty : ∀ a i, (rows a i).Nonempty

/-- A stationary (deterministic, Markov) controller policy `π = (𝐚, 𝐚, …)`, `𝐚 : 𝒳 → 𝒜`,
the same decision rule at every stage; the space `Π_s` (p. 782). -/
abbrev StationaryPolicy (n : ℕ) (A : Type) := Fin n → A

/-- A stationary admissible policy of nature, an element of `𝒯_s` (p. 781): one collection of
transition matrices `(P^a)_{a ∈ 𝒜}` used at every stage, where the `i`-th row `P a i` of `P^a`
lies in `𝒫_i^a`, chosen independently for each `(a, i)`. `P a i j` is the probability of moving
from state `i` to state `j` under action `a`. -/
abbrev Model.StationaryNature {n : ℕ} {A : Type} (M : Model n A) :=
  {P : A → Fin n → Fin n → ℝ // ∀ a i, P a i ∈ M.rows a i}

end RobustMDP.Discounted
