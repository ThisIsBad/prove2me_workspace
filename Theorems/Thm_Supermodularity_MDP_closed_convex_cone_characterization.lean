import Mathlib

open MeasureTheory

namespace Supermodularity.MDP

/-- Theorem 3.9.1 (p. 159–160, PDF 172–173). `T` is a subset of `Rᵐ`, `{F(t,w) : t ∈ T}`
is a collection of distribution functions on `Rⁿ` (represented by measures `μ t`), and `V`
is a closed (in the topology of pointwise convergence on `T → ℝ`) convex cone of
real-valued functions on `T`. Then `∫_S dF(t,w) ∈ V` for every increasing set `S ⊆ Rⁿ` iff
`∫ h(w) dF(t,w) ∈ V` for every increasing real-valued `h` on `Rⁿ`. -/
theorem closed_convex_cone_characterization {m n : ℕ} (T : Set (Fin m → ℝ))
    (μ : (Fin m → ℝ) → Measure (Fin n → ℝ)) (V : Set (T → ℝ))
    (hVclosed : IsClosed V)
    (hVadd : ∀ ⦃f g : T → ℝ⦄, f ∈ V → g ∈ V → f + g ∈ V)
    (hVsmul : ∀ ⦃f : T → ℝ⦄, f ∈ V → ∀ ⦃c : ℝ⦄, 0 ≤ c → c • f ∈ V) :
    (∀ ⦃S : Set (Fin n → ℝ)⦄, IsUpperSet S →
        (fun t : T => (μ (t : Fin m → ℝ) S).toReal) ∈ V) ↔
      (∀ ⦃h : (Fin n → ℝ) → ℝ⦄, Monotone h →
        (∀ t : T, Integrable h (μ (t : Fin m → ℝ))) →
        (fun t : T => ∫ w, h w ∂ (μ (t : Fin m → ℝ))) ∈ V) := by sorry

end Supermodularity.MDP
