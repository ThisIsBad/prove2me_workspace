import Mathlib
import Definitions.Def_GravesWillems_Serial_backlog
import Definitions.Def_GravesWillems_Serial_programP
open MeasureTheory

namespace GravesWillems.Serial

/-- Eqs. (A7)–(A8) of Graves–Willems 2000 (Appendix, pp. 81–82): let `B*` be feasible for `P*`,
`1 ≤ k < N`, the constraints (A3) with index `1, …, k − 1` binding and the `k`-th strict. With
`Δ = B*_k − D(Σ_{i=1}^k Tᵢ) + D(Σ_{i=1}^{k−1} Tᵢ)`, the vector `B**` obtained by moving `Δ` from
stage `k` to stage `k + 1` is feasible, binds the constraints `1, …, k`, and, when `D(0) = 0`,
`D` is nondecreasing and the echelon holding costs `e_i = hᵢ − h_{i+1}` (`1 ≤ i < N`) are
nonnegative, has objective value no greater than that of `B*` at every period `t`. -/
theorem transfer_step_improves {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (d : Ω → ℤ → ℝ) (hd : ∀ τ : ℤ, Integrable (fun ω => d ω τ) μ)
    (N : ℕ) (T : ℕ → ℕ) (D : ℕ → ℝ) (hD0 : D 0 = 0) (hD : Monotone D)
    (h : ℕ → ℝ) (he : ∀ i ∈ Finset.Ico 1 N, 0 ≤ h i - h (i + 1))
    (B : ℕ → ℝ) (hB : Feasible N T D B) (k : ℕ) (hk1 : 1 ≤ k) (hkN : k + 1 ≤ N)
    (hbind : ∀ i ∈ Finset.Ico 1 k,
      ∑ m ∈ Finset.Icc 1 i, B m = D (∑ m ∈ Finset.Icc 1 i, T m))
    (hstrict : D (∑ m ∈ Finset.Icc 1 k, T m) < ∑ m ∈ Finset.Icc 1 k, B m) :
    Feasible N T D (transfer B k (B k - D (∑ m ∈ Finset.Icc 1 k, T m)
        + D (∑ m ∈ Finset.Icc 1 (k - 1), T m))) ∧
    (∀ i ∈ Finset.Icc 1 k,
      ∑ m ∈ Finset.Icc 1 i, transfer B k (B k - D (∑ m ∈ Finset.Icc 1 k, T m)
          + D (∑ m ∈ Finset.Icc 1 (k - 1), T m)) m
        = D (∑ m ∈ Finset.Icc 1 i, T m)) ∧
    ∀ t : ℤ,
      objective μ d N T h (transfer B k (B k - D (∑ m ∈ Finset.Icc 1 k, T m)
          + D (∑ m ∈ Finset.Icc 1 (k - 1), T m))) t
        ≤ objective μ d N T h B t := by sorry

end GravesWillems.Serial
