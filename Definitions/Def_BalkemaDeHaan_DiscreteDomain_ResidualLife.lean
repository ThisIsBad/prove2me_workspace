import Mathlib
import Definitions.Def_BalkemaDeHaan_LimitTypes_ResidualLife

open MeasureTheory ProbabilityTheory Filter Topology

namespace BalkemaDeHaan.DiscreteDomain

/-- The domain of residual life time attraction `D_r(G)` (p. 798, PDF 7): the law `μ` (with
distribution function `F`) belongs to `D_r(G)` iff `F(x) < 1` for all `x` and there are
normalizing functions `a(t) > 0` and `b(t)` with `F_t(b(t) + x a(t)) → G(x)` weakly as `t → ∞`.
The page notes that `F ∈ D_r(G)` implies `F(x) < 1` for all `x`; it is built into the
definition, since `F_t` is undefined otherwise. -/
def InDr (μ : Measure ℝ) (G : ℝ → ℝ) : Prop :=
  (∀ x, 0 < μ (Set.Ioi x)) ∧
  ∃ a b : ℝ → ℝ, (∀ t, 0 < a t) ∧
    BalkemaDeHaan.LimitTypes.WeakConv (fun t x => BalkemaDeHaan.LimitTypes.residualCDF μ t (b t + x * a t)) G

end BalkemaDeHaan.DiscreteDomain
