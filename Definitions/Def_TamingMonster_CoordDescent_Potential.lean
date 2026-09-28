import Mathlib
import Definitions.Def_TamingMonster_CoordDescent_Setting

namespace TamingMonster.CoordDescent

variable {X : Type*} {K t : ℕ}

/-- The unnormalized relative entropy between two nonnegative vectors on `A` (§5, p. 9):
`RE(p ‖ q) = ∑_{a ∈ A} (p_a ln(p_a / q_a) + q_a − p_a)`. -/
noncomputable def relEntropy (p q : Fin K → ℝ) : ℝ :=
  ∑ a, (p a * Real.log (p a / q a) + q a - p a)

/-- The uniform distribution `U_A` on `A = Fin K`. -/
noncomputable def uniformA (K : ℕ) : Fin K → ℝ := fun _ => 1 / (K : ℝ)

/-- The potential function, Eq. (6) (p. 9), for the history `H_τ` of length `τ = t` and minimum
probability `μ`:
`Φ(Q) = τμ ( Ê_x[RE(U_A ‖ Q^μ(· | x))] / (1 − Kμ) + ∑_{π ∈ Π} Q(π) b_π / (2K) )`. -/
noncomputable def potential (Pi : Finset (X → Fin K)) (H : History X K t) (μ : ℝ)
    (Q : Pi → ℝ) : ℝ :=
  (t : ℝ) * μ *
    (empExp H (fun x => relEntropy (uniformA K) (smoothedProj Pi μ Q x)) / (1 - (K : ℝ) * μ)
      + (∑ π, Q π * bCoef Pi H μ (π : X → Fin K)) / (2 * (K : ℝ)))

end TamingMonster.CoordDescent
