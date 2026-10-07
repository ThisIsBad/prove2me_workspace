import Mathlib
import Definitions.Def_LawlerWCT_RhoMax_Model

namespace LawlerWCT.RhoMax

theorem max_weight_initial_set_rhoMaximal {ι : Type*} [DecidableEq ι] (N : Finset ι)
    (G : ι → ι → Prop) (hGN : ∀ i j, G i j → i ∈ N ∧ j ∈ N)
    (hacyc : ∀ j, ¬ Relation.TransGen G j j)
    (w p : ι → ℤ) (wstar pstar : ℤ)
    (hw : ∀ j ∈ N, -wstar ≤ w j ∧ w j ≤ wstar) (hpb : ∀ j ∈ N, 1 ≤ p j ∧ p j ≤ pstar)
    (Istar : Finset ι)
    (hIstar : LawlerWCT.SeriesPar.IsRhoMaximal G (fun j => (p j : ℝ)) (fun j => (w j : ℝ)) N Istar)
    (ρ : ℝ)
    (hlo : ρ ≤ LawlerWCT.SeriesPar.rho (fun j => (p j : ℝ)) (fun j => (w j : ℝ)) Istar)
    (hhi : LawlerWCT.SeriesPar.rho (fun j => (p j : ℝ)) (fun j => (w j : ℝ)) Istar ≤
      ρ + 1 / ((N.card : ℝ) * (pstar : ℝ)) ^ 2) :
    ∀ I, LawlerWCT.SeriesPar.IsInitialSet G N I → I.Nonempty →
      (∀ I', LawlerWCT.SeriesPar.IsInitialSet G N I' →
        trialWeight (fun j => (p j : ℝ)) (fun j => (w j : ℝ)) ρ I' ≤
          trialWeight (fun j => (p j : ℝ)) (fun j => (w j : ℝ)) ρ I) →
      LawlerWCT.SeriesPar.IsRhoMaximal G (fun j => (p j : ℝ)) (fun j => (w j : ℝ)) N I := by sorry

end LawlerWCT.RhoMax

