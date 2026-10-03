import Mathlib
import Definitions.Def_SennottDP_Fatou_Basic

open Filter Topology
open scoped ENNReal

namespace SennottDP.Fatou

/-- Sennott (1999), Theorem A.2.6 (Generalized Dominated Convergence Theorem), p. 278.
(i)–(iii) of Proposition A.2.5 are `ApproxDist P SN Q` (`Q N j = P_j(N)`); (iv) `u(j, N)`, `w(j, N)`
are finite functions of `j ∈ S_N` and `N` with `|u| ≤ w`; (v) `lim_N u(·, N) = u(·)` and
`lim_N w(·, N) = w(·)` exist (limits in `[−∞, ∞]`); (vi) `lim_N ∑_{j ∈ S_N} P_j(N) w(j, N)` exists and
equals `∑_{j ∈ S} P_j w(j) < ∞`. Then `lim_N ∑_{j ∈ S_N} P_j(N) u(j, N)` exists and equals
`∑_{j ∈ S} P_j u(j)`. -/
theorem generalized_dominated_convergence {S : Type*} [Countable S] {P : S → ℝ≥0∞}
    {SN : ℕ → Set S} {Q : ℕ → S → ℝ≥0∞} (hA : ApproxDist P SN Q)
    (u w : S → ℕ → ℝ) (hdom : ∀ N, ∀ j ∈ SN N, |u j N| ≤ w j N)
    (uL wL : S → EReal)
    (hu : ∀ j, Tendsto (fun N => (u j N : EReal)) atTop (𝓝 (uL j)))
    (hw : ∀ j, Tendsto (fun N => (w j N : EReal)) atTop (𝓝 (wL j)))
    (hsum : Tendsto (fun N => wsum ((SN N).indicator (Q N)) (fun j => (w j N : EReal))) atTop
      (𝓝 (wsum P wL)))
    (hfin : wsum P wL < ⊤) :
    Tendsto (fun N => wsum ((SN N).indicator (Q N)) (fun j => (u j N : EReal))) atTop
      (𝓝 (wsum P uL)) := by sorry

end SennottDP.Fatou
