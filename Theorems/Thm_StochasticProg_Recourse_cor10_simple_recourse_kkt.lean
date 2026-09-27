import Mathlib
import Definitions.Def_StochasticProg_Recourse_SimpleRecourse

namespace StochasticProg.Recourse

variable {n1 m1 m2 : ℕ}

/-- Chapter 3, Corollary 10 (p. 116): the specialization of Theorem 9 to simple
recourse, using the explicit subdifferential form `∂Q_i(x) = {πT_i· | -q⁺_i +
q_iF⁻_i(T_i·x) ≤ π ≤ -q⁺_i + q_iF⁺_i(T_i·x)}` of Eq. (1.10), where `F⁻_i, F⁺_i` are
the left- and right-hand limits of the distribution function of `h_i` (p. 114); the
book states (1.10) directly rather than deriving it from the second-stage LP, so
`hsubdiff` records that same closed form here as a hypothesis rather than as a
derived fact. `Q` (the aggregate simple-recourse value, Eq. (1.9)) is left abstract,
constrained only by `hsubdiff` and by the subgradient inequality it packages,
exactly as the book leaves it in this corollary. -/
theorem cor10_simple_recourse_kkt (inst : SimpleRecourseInstance n1 m1 m2)
    (Fminus Fplus : Fin m2 → ℝ → ℝ) (Q : (Fin n1 → ℝ) → EReal) (hQ : ∀ x, Q x ≠ ⊥)
    (hsubdiff : ∀ x : Fin n1 → ℝ,
      {η : Fin n1 → ℝ | ∀ y : Fin n1 → ℝ,
          Q x + ((dotProduct η (y - x) : ℝ) : EReal) ≤ Q y} =
        {η | ∃ pi : Fin m2 → ℝ,
          (∀ i, -(inst.qplus i) + inst.qsum i * Fminus i (Matrix.mulVec inst.T x i) ≤ pi i ∧
                pi i ≤ -(inst.qplus i) + inst.qsum i * Fplus i (Matrix.mulVec inst.T x i)) ∧
          η = fun j => ∑ i, pi i * inst.T i j})
    (hfin : ∃ z0 : ℝ,
      sInf ((fun x => ((dotProduct inst.c x : ℝ) : EReal) + Q x) '' inst.K1) = (z0 : EReal))
    (xstar : Fin n1 → ℝ) (hx : xstar ∈ inst.K1) :
    (((dotProduct inst.c xstar : ℝ) : EReal) + Q xstar =
        sInf ((fun x => ((dotProduct inst.c x : ℝ) : EReal) + Q x) '' inst.K1)) ↔
      ∃ (lam : Fin m1 → ℝ) (mu : Fin n1 → ℝ) (pi : Fin m2 → ℝ),
        (∀ j, 0 ≤ mu j) ∧ dotProduct mu xstar = 0 ∧
        (∀ i, -(inst.qplus i) + inst.qsum i * Fminus i (Matrix.mulVec inst.T xstar i) ≤ pi i ∧
              pi i ≤ -(inst.qplus i) + inst.qsum i * Fplus i (Matrix.mulVec inst.T xstar i)) ∧
        (fun j => -inst.c j + Matrix.mulVec (Matrix.transpose inst.A) lam j + mu j -
            ∑ i, pi i * inst.T i j) = 0 := by sorry

end StochasticProg.Recourse

