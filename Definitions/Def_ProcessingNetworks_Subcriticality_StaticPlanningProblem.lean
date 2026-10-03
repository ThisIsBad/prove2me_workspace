import Mathlib
import Definitions.Def_ProcessingNetworks_Subcriticality_SPNPlanningData

namespace ProcessingNetworks.Subcriticality

/-- Feasibility of the static planning problem (SPP) at level `γ` for arrival-rate vector `λ`,
Eqs. (5.5)-(5.8), p. 93 (PDF p. 109): `x` is a nonnegative activity-rate vector satisfying the
material balance constraint `Rx = λ` (5.6) and the capacity constraint `Ax ≤ γb` (5.7)-(5.8). -/
def SPPFeasible {I J K : ℕ} (D : SPNPlanningData I J K) (γ : ℝ) (lam : Fin I → ℝ)
    (x : Fin J → ℝ) : Prop :=
  D.R.mulVec x = lam ∧ (∀ j, 0 ≤ x j) ∧ ∀ k, (D.A.mulVec x) k ≤ γ * D.b k

/-- `γ*` is the optimal objective value of the SPP for arrival-rate vector `λ`: the least `γ` for
which the SPP (5.5)-(5.8) is feasible. -/
def IsOptimalSPPValue {I J K : ℕ} (D : SPNPlanningData I J K) (lam : Fin I → ℝ)
    (γstar : ℝ) : Prop :=
  IsLeast {γ : ℝ | ∃ x, SPPFeasible D γ lam x} γstar

/-- The subcritical region `Λ`, Eq. (5.16), p. 94 (PDF p. 110): nonnegative arrival-rate vectors
`λ ∈ ℝ^I_+` for which the SPP's optimal objective value is strictly less than `1`. -/
def SubcriticalRegion {I J K : ℕ} (D : SPNPlanningData I J K) : Set (Fin I → ℝ) :=
  {lam | (∀ i, 0 ≤ lam i) ∧ ∃ γstar, IsOptimalSPPValue D lam γstar ∧ γstar < 1}

/-- Feasibility of the augmented static planning problem for alternate routing with immediate
commitment, Eqs. (5.10), (5.11), (5.13)-(5.15), p. 99 (PDF p. 115): the decision variables are
extended to include the `L × I` routing matrix `φ` (`φ ℓ i = 0` whenever routing option `G ℓ i`
is unavailable, and `φ`'s row sums match the source arrival rates `ν`), with `λ` derived from `φ`
via (5.11) and folded into the ordinary SPP constraints (5.13)-(5.15), `φ, x ≥ 0` (5.15). -/
def AugmentedSPPFeasible {I J K L : ℕ} (D : SPNPlanningData I J K) (G : Matrix (Fin L) (Fin I) ℝ)
    (γ : ℝ) (nu : Fin L → ℝ) (phi : Fin L → Fin I → ℝ) (x : Fin J → ℝ) : Prop :=
  (∀ ℓ i, G ℓ i = 0 → phi ℓ i = 0) ∧ (∀ ℓ, ∑ i, phi ℓ i = nu ℓ) ∧
  D.R.mulVec x = (fun i => ∑ ℓ, phi ℓ i) ∧ (∀ ℓ i, 0 ≤ phi ℓ i) ∧ (∀ j, 0 ≤ x j) ∧
  ∀ k, (D.A.mulVec x) k ≤ γ * D.b k

/-- Optimal objective value of the augmented SPP, for a given source-rate vector `ν`. -/
def IsOptimalAugmentedSPPValue {I J K L : ℕ} (D : SPNPlanningData I J K)
    (G : Matrix (Fin L) (Fin I) ℝ) (nu : Fin L → ℝ) (γstar : ℝ) : Prop :=
  IsLeast {γ : ℝ | ∃ phi x, AugmentedSPPFeasible D G γ nu phi x} γstar

/-- Subcriticality for the alternate-routing model, "as that term was defined in the last
paragraph of Section 5.2" (p. 99, PDF p. 115): the augmented SPP's optimal objective value is
strictly less than `1`. -/
def IsAugmentedSubcritical {I J K L : ℕ} (D : SPNPlanningData I J K)
    (G : Matrix (Fin L) (Fin I) ℝ) (nu : Fin L → ℝ) : Prop :=
  ∃ γstar, IsOptimalAugmentedSPPValue D G nu γstar ∧ γstar < 1

end ProcessingNetworks.Subcriticality
