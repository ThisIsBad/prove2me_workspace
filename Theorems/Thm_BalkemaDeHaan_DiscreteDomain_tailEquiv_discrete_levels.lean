import Mathlib
import Definitions.Def_BalkemaDeHaan_DiscreteDomain_ResidualLife
import Definitions.Def_BalkemaDeHaan_DiscreteDomain_PiPC
import Definitions.Def_BalkemaDeHaan_DiscreteDomain_DiscreteLaw

open MeasureTheory Filter Topology

namespace BalkemaDeHaan.DiscreteDomain

/-- Proof of Theorem 5, p. 800 (PDF 9): if `F = 1 - R ∈ D_r(Π_{p,c})`, there is a sequence
`b_n ↑ ∞` with `R(b_{n+1})/R(b_n) → e^{-p}`, and `F` is BalkemaDeHaan.LimitTypes.tail equivalent to a discrete law `F₀`
with jumps `t₀ < t₁ < ⋯ → ∞` taking only the values `F(b_n)`: `F₀(s) = F(b_n)` for
`t_n ≤ s < t_{n+1}`, i.e. `R₀(t_n) = R(b_n)`. -/
theorem tailEquiv_discrete_levels (p c : ℝ) (hp : 0 < p) (hc : 0 ≤ c)
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ : InDr μ (piPC p c)) :
    ∃ b : ℕ → ℝ, StrictMono b ∧ Tendsto b atTop atTop ∧
      Tendsto (fun n : ℕ => (μ (Set.Ioi (b (n + 1)))).toReal / (μ (Set.Ioi (b n))).toReal)
        atTop (𝓝 (Real.exp (-p))) ∧
      ∃ ν₀ : Measure ℝ, IsProbabilityMeasure ν₀ ∧ ∃ t : ℕ → ℝ,
        IsDiscreteWithJumps ν₀ t ∧ (∀ n, ν₀ (Set.Ioi (t n)) = μ (Set.Ioi (b n))) ∧
        TailEquiv μ ν₀ := by sorry

end BalkemaDeHaan.DiscreteDomain

