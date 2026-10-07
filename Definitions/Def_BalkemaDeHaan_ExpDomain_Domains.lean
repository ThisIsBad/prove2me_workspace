import Definitions.Def_BalkemaDeHaan_ExpDomain_Distribution
import Definitions.Def_BalkemaDeHaan_ExpDomain_Laws

namespace BalkemaDeHaan.ExpDomain

open Filter MeasureTheory ProbabilityTheory

/-- The paper's `D₀`: lifetime laws with no finite upper endpoint. -/
def InDZero (μ : Measure ℝ) : Prop :=
  ∀ x : ℝ, 0 < μ (Set.Ioi x)

/-- The domain `D_r(G)` using §2's shift of the residual lifetime `X - t`. -/
def InDr (μ : Measure ℝ) (G : ℝ → ℝ) : Prop :=
  InDZero μ ∧ ∃ a b : ℝ → ℝ, (∀ t : ℝ, 0 < a t) ∧
    WeakConvergenceReal (fun t x => BalkemaDeHaan.LimitTypes.residualCDF μ t (b t + x * a t)) G

/-- The extreme-value domain `D(G)` of normalized sample maxima. -/
def InD (μ : Measure ℝ) (G : ℝ → ℝ) : Prop :=
  ∃ a b : ℕ → ℝ, (∀ n : ℕ, 0 < a n) ∧
    WeakConvergenceNat (fun n x => (cdf μ (a n * x + b n)) ^ n) G

/-- Equation (11), on a specified range of abscissas. -/
def TailScaledConvergence (μ : Measure ℝ) (a b : ℕ → ℝ) (U : Set ℝ) : Prop :=
  ∀ x : ℝ, x ∈ U →
    Tendsto (fun n : ℕ => (n : ℝ) * BalkemaDeHaan.LimitTypes.tail μ (b n + x * a n)) atTop (nhds (Real.exp (-x)))

end BalkemaDeHaan.ExpDomain
