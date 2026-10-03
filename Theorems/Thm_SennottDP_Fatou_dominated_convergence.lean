import Mathlib
import Definitions.Def_SennottDP_Fatou_Basic

open Filter Topology
open scoped ENNReal

namespace SennottDP.Fatou

/-- Sennott (1999), Theorem A.2.3 (Dominated Convergence Theorem), p. 276.
(i) `S` is countable with probability distribution `(P_j)`; (ii) `u(j, N)`, `w(j, N)` are finite
with `|u| ≤ w`; (iii) `lim_N u(·, N) = u(·)` and `lim_N w(·, N) = w(·)` exist (limits in `[−∞, ∞]`);
(iv) `lim_N ∑_j P_j w(j, N)` exists and equals `∑_j P_j w(j) < ∞`. Then
`lim_N ∑_j P_j u(j, N)` exists and equals `∑_j P_j u(j)`. -/
theorem dominated_convergence {S : Type*} [Countable S] (P : S → ℝ≥0∞) (hP : ∑' j, P j = 1)
    (u w : S → ℕ → ℝ) (hdom : ∀ j N, |u j N| ≤ w j N)
    (uL wL : S → EReal)
    (hu : ∀ j, Tendsto (fun N => (u j N : EReal)) atTop (𝓝 (uL j)))
    (hw : ∀ j, Tendsto (fun N => (w j N : EReal)) atTop (𝓝 (wL j)))
    (hsum : Tendsto (fun N => wsum P (fun j => (w j N : EReal))) atTop (𝓝 (wsum P wL)))
    (hfin : wsum P wL < ⊤) :
    Tendsto (fun N => wsum P (fun j => (u j N : EReal))) atTop (𝓝 (wsum P uL)) := by sorry

end SennottDP.Fatou
