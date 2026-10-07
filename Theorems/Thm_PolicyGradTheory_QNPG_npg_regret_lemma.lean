import Mathlib
import Definitions.Def_PolicyGradTheory_ProjGA_MDP

namespace PolicyGradTheory.QNPG

open FoundationsML.ReinforcementLearning

/-- Lemma 6.2, pp. 37–38, the deterministic NPG regret lemma. -/
theorem npg_regret_lemma {S A : Type} [Fintype S] [DecidableEq S]
    [Fintype A] [DecidableEq A] [Nonempty A] {d : ℕ}
    (P : S → A → S → ℝ) (r : S → A → ℝ) (γ : ℝ)
    (hM : PolicyGradTheory.ProjGA.IsFiniteMDP P r γ)
    (ρ : S → ℝ) (hρ : PolicyGradTheory.ProjGA.IsDist ρ)
    (πtilde : S → A → ℝ) (hπtilde : IsPolicy πtilde)
    (pol : EuclideanSpace ℝ (Fin d) → S → A → ℝ)
    (hpol : ∀ x, IsPolicy (pol x))
    (hpos : ∀ x s a, 0 < pol x s a)
    (β : ℝ) (hβ : 0 ≤ β)
    (hdiff : ∀ s a, Differentiable ℝ (fun z => Real.log (pol z s a)))
    (hsmooth : ∀ s a x y,
      ‖gradient (fun z => Real.log (pol z s a)) x -
        gradient (fun z => Real.log (pol z s a)) y‖ ≤ β * ‖x - y‖)
    (η W : ℝ) (hη : 0 < η)
    (T : ℕ) (hT : 0 < T)
    (θ w : ℕ → EuclideanSpace ℝ (Fin d))
    (hupdate : ∀ t < T, θ (t + 1) = θ t + η • w t)
    (hinit : ∀ s a, pol (θ 0) s a = 1 / (Fintype.card A : ℝ))
    (hw : ∀ t ≤ T, ‖w t‖ ≤ W) :
    ∃ t : ℕ, t < T ∧
      PolicyGradTheory.ProjGA.valueAt πtilde P r γ ρ - PolicyGradTheory.ProjGA.valueAt (pol (θ t)) P r γ ρ ≤
        (1 / (1 - γ)) *
          (Real.log (Fintype.card A : ℝ) / (η * T) + η * β * W ^ 2 / 2 +
            (1 / (T : ℝ)) * ∑ i ∈ Finset.range T,
              ∑ s : S, PolicyGradTheory.ProjGA.visitation πtilde P γ ρ s *
                ∑ a : A, πtilde s a *
                  (PolicyGradTheory.ProjGA.advantage (pol (θ i)) P r γ s a -
                    inner ℝ (w i) (gradient (fun z => Real.log (pol z s a)) (θ i)))) := by sorry

end PolicyGradTheory.QNPG

