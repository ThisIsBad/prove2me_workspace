import Mathlib
import Definitions.Def_LawlerWCT_RhoMax_Model

namespace LawlerWCT.RhoMax

theorem rho_separation {ι : Type*} (N : Finset ι) (w p : ι → ℤ) (pstar : ℤ)
    (hpb : ∀ j ∈ N, 1 ≤ p j ∧ p j ≤ pstar) (I I' : Finset ι) (hI : I ⊆ N) (hI' : I' ⊆ N)
    (hIne : I.Nonempty) (hI'ne : I'.Nonempty)
    (hne : LawlerWCT.SeriesPar.rho (fun j => (p j : ℝ)) (fun j => (w j : ℝ)) I ≠
      LawlerWCT.SeriesPar.rho (fun j => (p j : ℝ)) (fun j => (w j : ℝ)) I') :
    1 / ((N.card : ℝ) * (pstar : ℝ)) ^ 2 ≤
      |LawlerWCT.SeriesPar.rho (fun j => (p j : ℝ)) (fun j => (w j : ℝ)) I -
        LawlerWCT.SeriesPar.rho (fun j => (p j : ℝ)) (fun j => (w j : ℝ)) I'| := by sorry

end LawlerWCT.RhoMax

