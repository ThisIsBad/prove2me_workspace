import Mathlib

namespace FirstOrderOpt.Nonconvex

open scoped RealInnerProductSpace

/-- Theorem 6.5 (deterministic nonconvex mirror descent complexity). `Ψ := f + h` on the closed
convex `X`, `f` has `L`-Lipschitz gradient `fGrad`. The MD algorithm (6.2.18) generates `x` with
`x (k+1)` the generalized projection at `x k` using the exact gradient `fGrad (x k)`; `gX k :=
P_X(x k, fGrad (x k), γ k)` (6.2.20). `R` is chosen (6.2.19) to minimize `‖gX ·‖` over `1,…,N`. If
`0 < γ k ≤ 2/L` for every `k ∈ [1,N]` with strict inequality for at least one `k`, then
`‖gX R‖² ≤ L·DΨ² / Σ_{k=1}^N (γ k - Lγ k²/2)`, where `DΨ² = (Ψ(x 1) - Ψ*)/L` (6.2.22). -/
theorem nonconvex_md_bound {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (X : Set E) (f h : E → ℝ) (V : E → E → ℝ) (L : ℝ) (hL : 0 < L) (fGrad : E → E)
    (hSmooth : ∀ x ∈ X, ∀ y ∈ X, f y - f x - ⟪fGrad x, y - x⟫ ≤ (L / 2) * ‖y - x‖ ^ 2)
    (N : ℕ) (hN : 1 ≤ N)
    (x : ℕ → E) (γ : ℕ → ℝ) (gX : ℕ → E)
    (hx : ∀ k, x k ∈ X)
    (hxDef : ∀ k, 1 ≤ k → k ≤ N → ∀ u ∈ X,
      ⟪fGrad (x k), x (k + 1)⟫ + (1 / γ k) * V (x k) (x (k + 1)) + h (x (k + 1)) ≤
        ⟪fGrad (x k), u⟫ + (1 / γ k) * V (x k) u + h u)
    (hgX : ∀ k, 1 ≤ k → k ≤ N → gX k = (1 / γ k) • (x k - x (k + 1)))
    (hγpos : ∀ k, 1 ≤ k → k ≤ N → 0 < γ k) (hγub : ∀ k, 1 ≤ k → k ≤ N → γ k ≤ 2 / L)
    (hγstrict : ∃ k, 1 ≤ k ∧ k ≤ N ∧ γ k < 2 / L)
    (R : ℕ) (hR : 1 ≤ R ∧ R ≤ N) (hRmin : ∀ k, 1 ≤ k → k ≤ N → ‖gX R‖ ≤ ‖gX k‖)
    (ΨStar : ℝ) (hΨStar : IsGLB ((fun x => f x + h x) '' X) ΨStar)
    (DΨ : ℝ) (hDΨ : DΨ = Real.sqrt ((f (x 1) + h (x 1) - ΨStar) / L)) :
    ‖gX R‖ ^ 2 ≤ (L * DΨ ^ 2) / ∑ k ∈ Finset.Icc 1 N, (γ k - L * (γ k) ^ 2 / 2) := by sorry

end FirstOrderOpt.Nonconvex

