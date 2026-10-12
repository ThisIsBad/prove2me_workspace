import Mathlib
import Definitions.Def_KelsoCrawford_OneSided_Model

namespace KelsoCrawford.OneSided

def fictitious {W : Type} [Fintype W] (v : Finset W → ℝ)
    (μ : W → ℝ → ℝ) : Market W (Fin (Fintype.card W + 1)) where
  u := fun i _ s => μ i s
  y := fun _ => v
  σ := fun _ _ => 0

noncomputable def employerPartition {W F : Type} [Fintype W] [DecidableEq W]
    (A : Allocation W F) : Finpartition (Finset.univ : Finset W) := by
  classical
  exact Finpartition.ofSetoid (Setoid.ker A.assign)

end KelsoCrawford.OneSided
