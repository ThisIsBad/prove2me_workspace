import Mathlib
import Definitions.Def_HighDimStat_Rkhs_Core

namespace HighDimStat.Rkhs

open scoped RealInnerProductSpace
open MeasureTheory

/-- Theorem 12.20 (Mercer's theorem, p. 395): suppose `X` is a compact metric space, `P` is a
finite measure on `X`, the kernel `K` is continuous, positive semidefinite, and satisfies the
Hilbert-Schmidt condition (12.11b) (the associated integral operator `TK` of (12.11a) is
represented here abstractly by a linear map on `L²(X;P)` tied to the integral formula via
`hTK`). Then there is a countable orthonormal basis `(φⱼ)_{j∈ι}` of `L²(X;P)` and non-negative
eigenvalues `(μⱼ)` with `TK(φⱼ) = μⱼφⱼ` for every `j` (Eq. 12.13a), and the kernel has the
expansion `K(x,z) = Σⱼ μⱼφⱼ(x)φⱼ(z)`, with the series converging both absolutely (pointwise
`HasSum`, for real-valued series equivalent to unconditional/absolute convergence) and, along
every enumeration of `ι` by `ℕ` (when one exists — vacuous when `ι` is finite, e.g. when
`L²(X;P)` itself is finite-dimensional, per Example 12.21), uniformly on `X × X` (Eq. 12.13b).
The index type `ι` is existentially quantified (Revision 1) rather than fixed to `ℕ`: pinning it
to `ℕ` would force `L²(X;P) ≃ ℓ²(ℕ,ℝ)`, which is false whenever `L²(X;P)` is finite-dimensional
(any finite `X`, e.g. Example 12.18/12.21's discrete case), making the original statement
mathematically false for a case the book's own text treats as an instance of this theorem. -/
theorem thm12_20_mercer {X : Type*} [MetricSpace X] [CompactSpace X] [MeasurableSpace X]
    [BorelSpace X] (P : Measure X) [IsFiniteMeasure P]
    (K : X → X → ℝ) (hKcont : Continuous (Function.uncurry K)) (hKpsd : IsPSDKernel K)
    (hHS : Integrable (fun p : X × X => (K p.1 p.2) ^ 2) (P.prod P))
    (TK : Lp ℝ 2 P →ₗ[ℝ] Lp ℝ 2 P)
    (hTK : ∀ f : Lp ℝ 2 P, (TK f : X → ℝ) =ᵐ[P] fun x => ∫ z, K x z * (f z) ∂P) :
    ∃ (ι : Type) (_ : Countable ι) (φ : HilbertBasis ι ℝ (Lp ℝ 2 P)) (μ : ι → ℝ),
      (∀ j, 0 ≤ μ j) ∧
      (∀ j, TK (φ j) = μ j • (φ j : Lp ℝ 2 P)) ∧
      (∀ x z, HasSum (fun j => μ j * (φ j : X → ℝ) x * (φ j : X → ℝ) z) (K x z)) ∧
      (∀ e : ℕ ≃ ι, TendstoUniformly (fun n : ℕ => fun p : X × X =>
          ∑ k ∈ Finset.range n, μ (e k) * (φ (e k) : X → ℝ) p.1 * (φ (e k) : X → ℝ) p.2)
        (Function.uncurry K) Filter.atTop) := by sorry

end HighDimStat.Rkhs
