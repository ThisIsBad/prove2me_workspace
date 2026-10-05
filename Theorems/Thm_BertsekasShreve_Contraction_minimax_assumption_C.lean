import Mathlib
import Definitions.Def_BertsekasShreve_Contraction_Model
import Definitions.Def_BertsekasShreve_Contraction_AssumptionC

namespace BertsekasShreve.Contraction

open Filter Topology

/-- Proposition 4.11, p. 69. The minimax model of Section 2.3.5 (p. 38):
`H(x, u, J) = sup_{w ∈ W(x,u)} {g(x, u, w) + α J[f(x, u, w)]}` (eq. (34)), with `W(x, u)` a nonempty
subset of `W` for `x ∈ S`, `u ∈ U(x)`, `f : SCW → S`, `g : SCW → R*`, `α > 0`, and `J₀ = 0`.
If `α < 1` and `0 ≤ g(x, u, w) ≤ b` for all `x ∈ S`, `u ∈ U(x)`, `w ∈ W`, then Assumption C holds
with `B̄ = B`, `m = 1`, and the scalars in (2) and (3) both equal to `α`. -/
theorem minimax_assumption_C {S C W : Type*} (P : Model S C) (Wset : S → C → Set W)
    (hW : ∀ x, ∀ u ∈ P.U x, (Wset x u).Nonempty) (g : S → C → W → EReal) (f : S → C → W → S)
    (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1)
    (hH : ∀ (x : S) (u : C) (J : S → EReal),
      P.H x u J = ⨆ w ∈ Wset x u, (g x u w + (α : EReal) * J (f x u w)))
    (hJ0 : P.J0 = fun _ => 0) (b : ℝ)
    (hg : ∀ x, ∀ u ∈ P.U x, ∀ w : W, 0 ≤ g x u w ∧ g x u w ≤ (b : EReal)) :
    AssumptionC P Set.univ 1 α α := by sorry

end BertsekasShreve.Contraction

