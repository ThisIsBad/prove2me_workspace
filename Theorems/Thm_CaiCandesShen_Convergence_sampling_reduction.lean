import Mathlib
import Definitions.Def_CaiCandesShen_Convergence_Iterations

namespace CaiCandesShen.Convergence

/-- §3.1, p. 1964: when `𝒜` is the sampling operator extracting the `m` entries with indices in
`Ω`, then `𝒜*𝒜 = P_Ω`, and for any `M` with `𝒜(M) = b`, setting `Y^k = 𝒜*(y^k)` turns a run of
(3.3) into a run of (2.7). -/
theorem sampling_reduction {n₁ n₂ m : ℕ} (ω : Fin m → Fin n₁ × Fin n₂)
    (hω : Function.Injective ω) (Ω : Finset (Fin n₁ × Fin n₂))
    (hΩ : Ω = Finset.univ.image ω) :
    (∀ X : Mat n₁ n₂, adjA (samplingOp ω) (applyA (samplingOp ω) X) = projΩ Ω X) ∧
    ∀ (τ : ℝ) (M : Mat n₁ n₂) (b : Fin m → ℝ) (δ : ℕ → ℝ) (X : ℕ → Mat n₁ n₂)
      (y : ℕ → Fin m → ℝ),
      applyA (samplingOp ω) M = b → IsUzawaSeq τ (samplingOp ω) b δ X y →
        IsSVTSeq τ Ω M δ X (fun k => adjA (samplingOp ω) (y k)) := by sorry

end CaiCandesShen.Convergence
