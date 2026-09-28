import Mathlib
import Definitions.Def_GravesWillems_Serial_backlog
open MeasureTheory

namespace GravesWillems.Serial

/-- The service constraints (A3) of Graves–Willems 2000 (Appendix, p. 81):
`B₁ + ⋯ + Bᵢ ≥ D(T₁ + ⋯ + Tᵢ)` for `i = 1, …, N`. -/
def ServiceConstraints (N : ℕ) (T : ℕ → ℕ) (D : ℕ → ℝ) (B : ℕ → ℝ) : Prop :=
  ∀ i ∈ Finset.Icc 1 N, D (∑ m ∈ Finset.Icc 1 i, T m) ≤ ∑ m ∈ Finset.Icc 1 i, B m

/-- Feasibility for program `P*` (Appendix, p. 81): the constraints (A3) and `Bᵢ ≥ 0` for
`i = 1, …, N`. -/
def Feasible (N : ℕ) (T : ℕ → ℕ) (D : ℕ → ℝ) (B : ℕ → ℝ) : Prop :=
  ServiceConstraints N T D B ∧ ∀ i ∈ Finset.Icc 1 N, 0 ≤ B i

/-- The objective of program `P*` (Appendix, p. 81) at period `t`:
`Σ_{i=1}^N hᵢBᵢ − Σ_{i=2}^N e_{i−1} E[Qᵢ(t)]`, with echelon holding cost `e_{i−1} = h_{i−1} − hᵢ`
and the expectation taken over the random demand path `d ω` under `μ`. -/
noncomputable def objective {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (d : Ω → ℤ → ℝ)
    (N : ℕ) (T : ℕ → ℕ) (h : ℕ → ℝ) (B : ℕ → ℝ) (t : ℤ) : ℝ :=
  ∑ i ∈ Finset.Icc 1 N, h i * B i
    - ∑ i ∈ Finset.Icc 2 N, (h (i - 1) - h i) * ∫ ω, backlog N T B (d ω) i t ∂μ

/-- The base-stock vector (A6) (Appendix, p. 81): `B₁ = D(T₁)` and
`Bᵢ = D(T₁ + ⋯ + Tᵢ) − D(T₁ + ⋯ + T_{i−1})` for `i = 2, …, N`; `0` at every other index. -/
noncomputable def a6 (N : ℕ) (T : ℕ → ℕ) (D : ℕ → ℝ) (i : ℕ) : ℝ :=
  if i = 1 then D (T 1)
  else if i ∈ Finset.Icc 2 N then
    D (∑ m ∈ Finset.Icc 1 i, T m) - D (∑ m ∈ Finset.Icc 1 (i - 1), T m)
  else 0

/-- The transfer of the proof of the Result (Appendix, p. 81): `B**ᵢ = Bᵢ` for `i ≠ k, k + 1`,
`B**_k = B_k − Δ`, `B**_{k+1} = B_{k+1} + Δ`. -/
noncomputable def transfer (B : ℕ → ℝ) (k : ℕ) (Δ : ℝ) : ℕ → ℝ :=
  Function.update (Function.update B k (B k - Δ)) (k + 1) (B (k + 1) + Δ)

end GravesWillems.Serial
