import Mathlib

open Filter Topology

namespace SennottDP.SEN

/-- Sennott (1999), Proposition B.6, p. 290: let `L(i)` and `M(i)` be nonnegative (finite)
functions on the countable set `S`. Assume `u_r(i)` is a sequence of functions on `S` with
`−L ≤ u_r ≤ M` for all `r`. Then there exist a subsequence `r_k` and a function `w`, with
`−L ≤ w ≤ M`, satisfying `lim_{k→∞} u_{r_k}(i) = w(i)` for all `i ∈ S`. -/
theorem prop_B_6_bounded_subsequence {S : Type} [Countable S] (L M : S → ℝ)
    (hL : ∀ i, 0 ≤ L i) (hM : ∀ i, 0 ≤ M i) (u : ℕ → S → ℝ)
    (hu : ∀ r i, -L i ≤ u r i ∧ u r i ≤ M i) :
    ∃ rk : ℕ → ℕ, StrictMono rk ∧ ∃ w : S → ℝ, (∀ i, -L i ≤ w i ∧ w i ≤ M i) ∧
      ∀ i, Tendsto (fun k => u (rk k) i) atTop (𝓝 (w i)) := by sorry

end SennottDP.SEN

