import Definitions.Def_LeastSquaresTD_Absorbing_Estimator

namespace LeastSquaresTD.Absorbing

variable {m : ℕ}

/-- Proof of Theorem 1, p. 44, Eq. (12), together with the paper's
claim that `θ*` is finite. The value function is the return series, so
summability at `γ = 1` remains part of this conclusion. -/
theorem value_consistency
    {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    (C : Chain X) (R : X → X → ℝ) (φ : X → Fin m → ℝ) (γ : ℝ)
    (habs : C.IsAbsorbing) (hRabs : ∀ x y, C.P x x = 1 → C.P y y = 1 → R x y = 0)
    (hm : m = Fintype.card C.Nonabsorbing)
    (hli : LinearIndependent ℝ (fun x : C.Nonabsorbing => φ x.val))
    (hφabs : ∀ x, C.P x x = 1 → φ x = 0)
    (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1) :
    ∃ θstar : Fin m → ℝ,
      (∀ x, Summable (fun k : ℕ => γ ^ k *
        (Matrix.mulVec (C.P ^ k) (C.rbar R)) x)) ∧
      (∀ x, C.value R γ x = ∑ i, φ x i * θstar i) ∧
      C.rbar R = Matrix.mulVec (1 - γ • C.P)
        (Matrix.mulVec (Matrix.of φ) θstar) := by sorry

end LeastSquaresTD.Absorbing

