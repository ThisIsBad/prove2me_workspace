import Mathlib
import Definitions.Def_RobustLS_LinFrac_Core

open Matrix

namespace RobustLS.LinFrac

/-- El Ghaoui & Lebret (1997), §2.2, Lemma 2.3, sufficiency, p. 1039 (PDF p. 5), **corrected**.
Let `𝒟` be a subspace of `ℝ^{N×N}`, `𝒮` (resp. `𝒢`) the symmetric (resp. skew-symmetric)
matrices commuting with every element of `𝒟`, `T₁ = T₁ᵀ ∈ ℝ^{d×d}`, `T₂ ∈ ℝ^{d×N}`,
`T₃ ∈ ℝ^{N×d}`, `T₄ ∈ ℝ^{N×N}`. If `S ∈ 𝒮`, `G ∈ 𝒢`, `S ≻ 0` and the block matrix of the lemma
is positive definite, then for every `Δ ∈ 𝒟` with `‖Δ‖ ≤ 1`: `det(I − T₄Δ) ≠ 0` and
`T(Δ) ≻ 0`.
Corrections to the printed lemma: (i) the extra hypothesis that `GΔ` is skew-symmetric for every
`Δ ∈ 𝒟` — this is exactly the identity `pᵀGq = 0` (`p = Δᵀq`) the proof uses; without it the
lemma is false (`N = 2`, `d = 1`, `𝒟 = span{I, J}` with `J = [[0,1],[−1,0]]`, `T₁ = 1`,
`T₂ = [1 0]`, `T₃ = GT₂ᵀ`, `T₄ = 0`, `S = sI` with `0 < s < 1`, `G = J`: the condition holds
but `T(J) = −1`); it holds automatically when every element of `𝒟` is symmetric or when
`G = 0`. (ii) The conclusion is the strict `T(Δ) ≻ 0`, which the same hypotheses give and which
§5.4 uses; the printed conclusion (9) is `T(Δ) ⪰ 0`, implied by it. -/
theorem lemma23_sufficiency {d N : ℕ} (𝒟 : Submodule ℝ (Matrix (Fin N) (Fin N) ℝ))
    (T₁ : Matrix (Fin d) (Fin d) ℝ) (hT₁ : T₁ = T₁ᵀ)
    (T₂ : Matrix (Fin d) (Fin N) ℝ) (T₃ : Matrix (Fin N) (Fin d) ℝ)
    (T₄ S G : Matrix (Fin N) (Fin N) ℝ) (hS : S ∈ symCommutant 𝒟) (hG : G ∈ skewCommutant 𝒟)
    (hGΔ : ∀ Δ ∈ 𝒟, (G * Δ)ᵀ = -(G * Δ)) (hSpos : S.PosDef)
    (hblock : (lemma23Block T₁ T₂ T₃ T₄ S G).PosDef) :
    ∀ Δ ∈ 𝒟, specNorm Δ ≤ 1 →
      (1 - T₄ * Δ).det ≠ 0 ∧ (lftT T₁ T₂ T₃ T₄ Δ).PosDef := by sorry

end RobustLS.LinFrac
