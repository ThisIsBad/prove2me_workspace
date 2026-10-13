import Mathlib
import Definitions.Def_MechanismDesign_Screening_Model
import Definitions.Def_MechanismDesign_Screening_NonlinearPricing

namespace MussaRosen.Mono

open MechanismDesign.Screening intervalIntegral

/-!
# Mussa and Rosen (1978), the monopolist's quality-assignment problem (§2, §4, pp. 303–309)

Consumer types `θ ∈ [θ̲, θ̄]` (`θlo`, `θhi`) are distributed with the density `D.f` of a
`TypeDistribution`; the cost of one unit of quality `q` is `C q`. An assignment `q : ℝ → ℝ`
gives the quality bought by type `θ`; only its values on `[θ̲, θ̄]` matter. None of the
definitions below carries the cost hypotheses: those are hypotheses of the theorems.
-/

variable {θlo θhi : ℝ}

/-- **Piecewise differentiable** (p. 308): `q` is differentiable at every point of `(θ̲, θ̄)`
outside some finite set. -/
def IsPiecewiseDiff (θlo θhi : ℝ) (q : ℝ → ℝ) : Prop :=
  ∃ s : Finset ℝ, ∀ θ ∈ Set.Ioo θlo θhi, θ ∉ s → DifferentiableAt ℝ q θ

/-- An **admissible assignment** (pp. 303, 308): nondecreasing on `[θ̲, θ̄]`, of feasible
quality `q(θ) ≥ 0` on `[θ̲, θ̄]`, and piecewise differentiable. -/
def IsAdmissible (θlo θhi : ℝ) (q : ℝ → ℝ) : Prop :=
  MonotoneOn q (Set.Icc θlo θhi) ∧ (∀ θ ∈ Set.Icc θlo θhi, 0 ≤ q θ) ∧ IsPiecewiseDiff θlo θhi q

/-- **Consumer surplus** `z(θ) = ∫_{θ̲}^{θ} q(s) ds`: equation (7) with the boundary condition
`z(θ*) = 0` (p. 307), in the form written on p. 315. -/
noncomputable def surplus (θlo : ℝ) (q : ℝ → ℝ) (θ : ℝ) : ℝ :=
  ∫ s in θlo..θ, q s

/-- The monopolist's **profit** (p. 308):
`Π(q) = ∫_{θ̲}^{θ̄} [θ q(θ) − z(θ) − C(q(θ))] f(θ) dθ`. -/
noncomputable def profit (D : TypeDistribution θlo θhi) (C : ℝ → ℝ) (q : ℝ → ℝ) : ℝ :=
  ∫ θ in θlo..θhi, (θ * q θ - surplus θlo q θ - C (q θ)) * D.f θ

/-- `q` is an **optimal** assignment (p. 308): it is admissible and no admissible assignment
yields a larger profit. -/
def IsOptimal (D : TypeDistribution θlo θhi) (C : ℝ → ℝ) (q : ℝ → ℝ) : Prop :=
  IsAdmissible θlo θhi q ∧ ∀ q' : ℝ → ℝ, IsAdmissible θlo θhi q' → profit D C q' ≤ profit D C q

/-- The **first variation** `Λ(h; q)` of the profit in the direction of a deformation `h`
(equation (9), p. 308):
`Λ(h; q) = ∫_{θ̲}^{θ̄} [θ h(θ) − ∫_{θ̲}^{θ} h(s) ds − C′(q(θ)) h(θ)] f(θ) dθ`. -/
noncomputable def firstVariation (D : TypeDistribution θlo θhi) (C q h : ℝ → ℝ) : ℝ :=
  ∫ θ in θlo..θhi, (θ * h θ - (∫ s in θlo..θ, h s) - deriv C (q θ) * h θ) * D.f θ

/-- The marginal profit `μ(t)` of a unit increase in quality for all types `θ ≥ t`, the first
line of equation (10), p. 309:
`μ(t) = ∫_t^{θ̄} [θ − ∫_t^{θ} ds − C′(q(θ))] f(θ) dθ`. -/
noncomputable def mu (D : TypeDistribution θlo θhi) (C q : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ θ in t..θhi, (θ - (∫ _s in t..θ, (1 : ℝ)) - deriv C (q θ)) * D.f θ

/-- The monopolist's profit with two consumer types (footnote 4, pp. 305–306): `n¹` consumers of
type `θ¹` buy quality `q^a`, `n²` consumers of type `θ²` buy quality `q^b`:
`n¹ (θ¹ q^a − C(q^a)) + n² (θ² q^b − (θ² − θ¹) q^a − C(q^b))`. -/
def twoTypeProfit (C : ℝ → ℝ) (θ1 θ2 n1 n2 qa qb : ℝ) : ℝ :=
  n1 * (θ1 * qa - C qa) + n2 * (θ2 * qb - (θ2 - θ1) * qa - C qb)

end MussaRosen.Mono
