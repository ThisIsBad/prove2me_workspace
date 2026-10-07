import Mathlib
import Definitions.Def_PoissonDirichlet_Ratio_Setting
open MeasureTheory ProbabilityTheory Filter Topology

namespace PoissonDirichlet.MaxDensity

/-- Size-biased pick, (2), p. 857: `W` is a size-biased pick from `(Vₙ)` if
`P(W = Vₙ | V₁, V₂, …) = Vₙ` for every `n`. 0-based: `V ω k` is `V_{k+1}`. Both `V` and `W`
are random variables (measurable), as the page presupposes; the conditional probability is
the conditional expectation of the indicator of `{W = V_{k+1}}` given `σ(V)`. -/
def IsSizeBiasedPick {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (V : Ω → ℕ → ℝ)
    (W : Ω → ℝ) : Prop :=
  Measurable V ∧ Measurable W ∧
    ∀ k : ℕ, P[(fun ω => if W ω = V ω k then (1 : ℝ) else 0) | MeasurableSpace.comap V inferInstance]
      =ᵐ[P] fun ω => V ω k

/-- Size-biased permutation, p. 857: `W 0` (paper `Ṽ₁`) is a size-biased pick from `(Vₙ)` and,
for every `m` and `j` (paper `n = m + 1`, `j + 1`),
`P(Ṽ_{n+1} = V_j | Ṽ₁, …, Ṽₙ; V₁, V₂, …) = V_j 1(V_j ≠ Ṽ_i for all i ≤ n) / (1 - Ṽ₁ - ⋯ - Ṽₙ)`. -/
def IsSizeBiasedPerm {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (V W : Ω → ℕ → ℝ) : Prop :=
  Measurable W ∧ IsSizeBiasedPick P V (fun ω => W ω 0) ∧
    ∀ m j : ℕ,
      P[(fun ω => if W ω (m + 1) = V ω j then (1 : ℝ) else 0) |
          MeasurableSpace.comap (fun ω => ((fun i : Fin (m + 1) => W ω i), V ω)) inferInstance]
        =ᵐ[P] fun ω =>
          (if ∀ i ≤ m, V ω j ≠ W ω i then V ω j else 0) /
            (1 - ∑ i ∈ Finset.range (m + 1), W ω i)

end PoissonDirichlet.MaxDensity
