import Mathlib
import Definitions.Def_RadGauss_Kernel_KernelClass

namespace RadGauss.Kernel

/-- §4.3, p. 477 (Bartlett–Mendelson 2002), the feature-map displays. Let `k` be a kernel on `𝒳`
with feature map `Φ : 𝒳 → ℋ` into a real Hilbert space, `k(x₁, x₂) = ⟨Φ(x₁), Φ(x₂)⟩`. Then
`‖Σ_i α_i Φ(x_i)‖² = Σ_{i,j} α_i α_j k(x_i, x_j)` for every finite family, and hence, for `B ≥ 0`,
`F ⊆ {x ↦ ⟨w, Φ(x)⟩ : ‖w‖ ≤ B}`. The paper takes `B > 0`; `0 ≤ B` is assumed here. -/
theorem feature_map_inclusion {X H : Type*} [TopologicalSpace X]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (k : X → X → ℝ) (hk : IsKernel k) (Φ : X → H)
    (hΦ : ∀ x₁ x₂, k x₁ x₂ = inner ℝ (Φ x₁) (Φ x₂)) (B : ℝ) (hB : 0 ≤ B) :
    (∀ (m : ℕ) (x : Fin m → X) (α : Fin m → ℝ),
        ‖∑ i, α i • Φ (x i)‖ ^ 2 = ∑ i, ∑ j, α i * α j * k (x i) (x j)) ∧
      kernelClass k B ⊆ {f | ∃ w : H, ‖w‖ ≤ B ∧ f = fun x => inner ℝ w (Φ x)} := by sorry

end RadGauss.Kernel

