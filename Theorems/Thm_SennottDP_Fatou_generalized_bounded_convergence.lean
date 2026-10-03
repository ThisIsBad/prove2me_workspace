import Mathlib
import Definitions.Def_SennottDP_Fatou_Basic

open Filter Topology
open scoped ENNReal

namespace SennottDP.Fatou

/-- Sennott (1999), Corollary A.2.7, p. 278. (i)–(iii) of Proposition A.2.5 are
`ApproxDist P SN Q`; (iv) `u(j, N)` is a function of `j ∈ S_N` and `N` with `lim_N u(·, N) = u(·)`;
(v) there is a finite constant `w` with `|u| ≤ w`. Then `lim_N ∑_{j ∈ S_N} P_j(N) u(j, N)` exists and
equals `∑_{j ∈ S} P_j u(j)`. -/
theorem generalized_bounded_convergence {S : Type*} [Countable S] {P : S → ℝ≥0∞}
    {SN : ℕ → Set S} {Q : ℕ → S → ℝ≥0∞} (hA : ApproxDist P SN Q)
    (u : S → ℕ → ℝ) (uL : S → EReal)
    (hu : ∀ j, Tendsto (fun N => (u j N : EReal)) atTop (𝓝 (uL j)))
    (w : ℝ) (hdom : ∀ N, ∀ j ∈ SN N, |u j N| ≤ w) :
    Tendsto (fun N => wsum ((SN N).indicator (Q N)) (fun j => (u j N : EReal))) atTop
      (𝓝 (wsum P uL)) := by sorry

end SennottDP.Fatou
