import Mathlib
import Definitions.Def_GoldieRenewal_Kesten_Perpetuity

namespace GoldieRenewal.Kesten

open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- **Proposition 4.2** [Grincevičius (1980)] (Goldie, *Implicit renewal theory and tails of
solutions of random equations*, Ann. Appl. Probab. 1(1) (1991), p. 136). Let `(Q_n, M_n)`,
`n = 1, 2, …`, be independent, each with the law `μ` of `(Q, M)`. With
`Π_j = M₁ ⋯ M_j`, `R_n = Σ_{k=1}^n Π_{k−1} Q_k`, `Π_{j,n} = Π_{k=j+1}^n M_k`,
`R_{j,n} = Σ_{k=j+1}^n Π_{j,k−1} Q_k`, for all `x, y ∈ ℝ`,
`P(max_{j=1,…,n} (R_j + Π_j med(R_{j,n} + Π_{j,n} y)) > x) ≤ 2 P(R_n + Π_n y > x)`.

**Formalization Note** The sequence is stored 0-based: `Q i`, `M i` (`i = 0, 1, …`) are the
paper's `Q_{i+1}`, `M_{i+1}` (see `piProd`, `partialSum`, `piProdFrom`, `partialSumFrom`).
`med X` is any median of the law of `X`; the paper fixes none, so the inequality is asserted for
every choice `med j` of medians, `j = 1, …, n`. "max > x" is "some `j ∈ {1, …, n}` has `… > x`".
No moment or Cramér condition is assumed, as in the paper. -/
theorem proposition_4_2 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (μ : Measure (ℝ × ℝ)) (Q M : ℕ → Ω → ℝ) (hQ : ∀ i, Measurable (Q i))
    (hM : ∀ i, Measurable (M i))
    (hindep : iIndepFun (fun i ω => (Q i ω, M i ω)) P)
    (hlaw : ∀ i, P.map (fun ω => (Q i ω, M i ω)) = μ)
    (n : ℕ) (x y : ℝ) (med : ℕ → ℝ)
    (hmed : ∀ j ∈ Finset.Icc 1 n,
      IsMedian (P.map (fun ω => partialSumFrom Q M j n ω + piProdFrom M j n ω * y)) (med j)) :
    P {ω | ∃ j ∈ Finset.Icc 1 n, x < partialSum Q M j ω + piProd M j ω * med j}
      ≤ 2 * P {ω | x < partialSum Q M n ω + piProd M n ω * y} := by sorry

end GoldieRenewal.Kesten

