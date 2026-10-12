import Mathlib
import Definitions.Def_KelsoCrawford_ContinuousCore_Model

namespace KelsoCrawford.ContinuousCore

theorem fine_grid_improves {W F : Type}
    [Fintype W] [DecidableEq W] [Fintype F] [DecidableEq F] [Nonempty F]
    (M : Market W F) (hu : M.UtilityRegular) (hMP : M.MP) (hNFL : M.NFL)
    (hres : M.ReservationSalaries)
    (hGS : ∀ j, KelsoCrawford.Process.GrossSubstitutesOn (M.y j) Set.univ)
    (H : ℝ) (hH : 0 < H)
    (hgain : ∀ A : Allocation W F, M.IsIR A →
      ∃ (j : F) (C : Finset W) (r : W → ℝ),
        (∀ i ∈ C, M.u i (A.assign i) (A.sal i) ≤ M.u i j (r i)) ∧
        KelsoCrawford.Process.profit (M.y j) (A.hired j) A.sal + H ≤ KelsoCrawford.Process.profit (M.y j) C r)
    (δ : ℝ) (hδ : 0 < δ) (hδsmall : δ < H / ((Fintype.card W : ℝ) + 1))
    (A : Allocation W F) (hIR : M.IsIR A)
    (hgrid : ∀ i, A.sal i ∈ M.grid δ i (A.assign i)) :
    M.CanStrictlyImprove (M.grid δ) A := by sorry

end KelsoCrawford.ContinuousCore

