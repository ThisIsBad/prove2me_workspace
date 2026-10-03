import Mathlib
import Definitions.Def_ProcessingNetworks_TaskAllocation_TaskAllocationModel

namespace ProcessingNetworks.TaskAllocation

/-- The fluid model equations (11.11)-(11.15), Dai & Harrison p. 217 (PDF p. 233), that hold for
the task allocation model under *any* simply structured routing policy (Theorem 11.4(b)): the
balance equation and nonnegativity (11.11); `Eh`/`Dh` nondecreasing and (jointly) globally
Lipschitz (11.12); the category-level arrival equation (11.13); the workload identity (11.14);
and, at each point where server `k`'s workload is positive, its aggregate departure rate is `1`
(11.15) — phrased, as throughout this series, via a hypothesised derivative vector `d` rather than
asserting the derivative exists, to avoid smuggling in an unproved differentiability claim. -/
def IsTaskAllocationFluidModelSolution {L K : ℕ} (dat : TaskAllocationData L K)
    (Eh Dh : ℝ → Fin L → Fin K → ℝ) (Wh : ℝ → Fin K → ℝ) (Zh : ℝ → Fin L → Fin K → ℝ) : Prop :=
  (∀ t : ℝ, 0 ≤ t → ∀ ℓ k, Zh t ℓ k = Zh 0 ℓ k + Eh t ℓ k - Dh t ℓ k) ∧
  (∀ t : ℝ, 0 ≤ t → ∀ ℓ k, 0 ≤ Zh t ℓ k) ∧
  ((∀ ℓ k, Monotone (fun t => Eh t ℓ k)) ∧ (∀ ℓ k, Monotone (fun t => Dh t ℓ k)) ∧
    ∃ Kc : ℝ, ∀ s t : ℝ, 0 ≤ s → s ≤ t → ∀ ℓ k,
      |Eh t ℓ k - Eh s ℓ k| ≤ Kc * (t - s) ∧ |Dh t ℓ k - Dh s ℓ k| ≤ Kc * (t - s)) ∧
  (∀ t : ℝ, 0 ≤ t → ∀ ℓ, ∑ k, Eh t ℓ k = dat.nu ℓ * t) ∧
  (∀ t : ℝ, 0 ≤ t → ∀ k, Wh t k = ∑ ℓ, dat.m ℓ k * Zh t ℓ k) ∧
  (∀ t : ℝ, 0 < t → ∀ k, 0 < Wh t k →
    ∀ d : Fin L → ℝ, (∀ ℓ, HasDerivAt (fun s => Dh s ℓ k) (d ℓ) t) → ∑ ℓ, dat.m ℓ k * d ℓ = 1)

/-- The WWTA-specific fluid equation (11.16), Dai & Harrison p. 217 (PDF p. 233): for each category
`ℓ`, `∑_k mℓk Ŵk(t) Ėℓk(t) = νℓ min_{k} mℓk Ŵk(t)`. Requires `Nonempty (Fin K)` (a task allocation
model with at least one server — the book's own tacit standing assumption, since (11.8)'s `argmin`
is over a nonempty server set `K`) for `⨅` to compute the genuine minimum rather than the junk
value `sInf ∅`. As with (11.15), phrased via a hypothesised derivative vector `d` for `Ė`. -/
def SatisfiesWWTAFluidEquation {L K : ℕ} [Nonempty (Fin K)] (dat : TaskAllocationData L K)
    (Eh : ℝ → Fin L → Fin K → ℝ) (Wh : ℝ → Fin K → ℝ) : Prop :=
  ∀ t : ℝ, 0 < t → ∀ ℓ : Fin L, ∀ d : Fin K → ℝ,
    (∀ k, HasDerivAt (fun s => Eh s ℓ k) (d k) t) →
    ∑ k, dat.m ℓ k * Wh t k * d k = dat.nu ℓ * ⨅ k, dat.m ℓ k * Wh t k

/-- A fluid model solution under the WWTA routing policy: (11.11)-(11.15) plus the WWTA-specific
(11.16) — the object Theorem 11.6 (the goal) proves stable. -/
def WWTAFluidModelSolution {L K : ℕ} [Nonempty (Fin K)] (dat : TaskAllocationData L K)
    (Eh Dh : ℝ → Fin L → Fin K → ℝ) (Wh : ℝ → Fin K → ℝ) (Zh : ℝ → Fin L → Fin K → ℝ) : Prop :=
  IsTaskAllocationFluidModelSolution dat Eh Dh Wh Zh ∧ SatisfiesWWTAFluidEquation dat Eh Wh

/-- Definition 6.3 (fluid model stability, mission III), specialized to the WWTA fluid model:
there is `γ > 0` such that every solution reaches the zero state by time `γ|Z(0)|`. -/
def WWTAFluidStable {L K : ℕ} [Nonempty (Fin K)] (dat : TaskAllocationData L K) : Prop :=
  ∃ γ : ℝ, 0 < γ ∧ ∀ (Eh Dh : ℝ → Fin L → Fin K → ℝ) (Wh : ℝ → Fin K → ℝ)
    (Zh : ℝ → Fin L → Fin K → ℝ),
    WWTAFluidModelSolution dat Eh Dh Wh Zh →
    ∀ t : ℝ, γ * (∑ ℓ, ∑ k, Zh 0 ℓ k) ≤ t → Zh t = fun _ _ => 0

end ProcessingNetworks.TaskAllocation
