import Mathlib

namespace HighDimStat.Pca

/-- The function `Ψ(Δ; P) := ⟨Δ, PΔ⟩ + 2⟨Δ, Pθ*⟩` of Wainwright, *High-Dimensional Statistics*
(2019), Eq. (8.13), central to the PCA basic inequality (Lemma 8.6). -/
def psiPCA {d : ℕ} (P : Matrix (Fin d) (Fin d) ℝ) (θstar Δ : Fin d → ℝ) : ℝ :=
  (∑ i, Δ i * (P.mulVec Δ) i) + 2 * (∑ i, Δ i * (P.mulVec θstar) i)

end HighDimStat.Pca
