import Mathlib
import Definitions.Def_ProcessingNetworks_ProportionalFairness_RestatedCore

namespace ProcessingNetworks.ProportionalFairness

/-- The data of a unitary network operating under PF control (Section 10.4), restated identically
from mission IX. -/
structure PFUnitaryNetworkData (I L : ℕ) where
  lam : Fin I → ℝ
  m : Fin I → ℝ
  hm : ∀ i, 0 < m i
  P : Matrix (Fin I) (Fin I) ℝ
  grp : Fin I → Fin L
  TildeAllocSet : Set (Fin L → ℝ)

/-- The total-arrival-rate vector `α` (Eq. 2.38), restated identically from mission IX. -/
def IsTotalArrivalRates {I L : ℕ} (dat : PFUnitaryNetworkData I L) (alpha : Fin I → ℝ) : Prop :=
  alpha = fun i => dat.lam i + ∑ k, dat.P k i * alpha k

/-- A point `t > 0` is regular for a fluid model solution `(A,D,T,Z)` (Definition 8.7), restated
identically from mission IX. -/
def RegularPoint {I : ℕ} (Ah Dh Th Zh : ℝ → Fin I → ℝ) (t : ℝ) : Prop :=
  DifferentiableAt ℝ Ah t ∧ DifferentiableAt ℝ Dh t ∧ DifferentiableAt ℝ Th t ∧
    DifferentiableAt ℝ Zh t

/-- Definition 10.3, Eqs. (10.29)-(10.35): the PF fluid model, restated identically from
mission IX; (10.34) asserts that whenever `Zᵢ(t) > 0` the derivative `d/dt Tᵢ(t)` exists and
equals `ψ̃_ℓ(Y(t)) Zᵢ(t)/Y_ℓ(t)` (the conclusion of Theorem 7.8). -/
def IsPFFluidModelSolution {I L : ℕ} (dat : PFUnitaryNetworkData I L)
    (Ah Dh Th Zh : ℝ → Fin I → ℝ) : Prop :=
  (∀ t : ℝ, 0 ≤ t → Zh t = fun i => Zh 0 i + Ah t i - Dh t i) ∧
  (∀ t : ℝ, 0 ≤ t → ∀ i, 0 ≤ Zh t i) ∧
  (∀ t : ℝ, 0 ≤ t → ∀ i, Ah t i = dat.lam i * t + ∑ k, dat.P k i * Dh t k) ∧
  (∀ t : ℝ, 0 ≤ t → ∀ i, Dh t i = Th t i / dat.m i) ∧
  (Th 0 = 0 ∧ Monotone Th ∧
    ∃ Kc : ℝ, ∀ s t : ℝ, 0 ≤ s → s ≤ t → ∀ i, |Th t i - Th s i| ≤ Kc * (t - s)) ∧
  (∀ t : ℝ, 0 < t → ∀ i, 0 < Zh t i →
    HasDerivAt (fun u => Th u i)
      (psi dat.TildeAllocSet (groupAggregate dat.grp (Zh t)) (dat.grp i) * Zh t i /
        groupAggregate dat.grp (Zh t) (dat.grp i)) t)

/-- Definition 6.3 (fluid model stability), specialized to the PF fluid model, restated
identically from mission IX. -/
def PFFluidStable {I L : ℕ} (dat : PFUnitaryNetworkData I L) : Prop :=
  ∃ γ : ℝ, 0 < γ ∧ ∀ (Ah Dh Th Zh : ℝ → Fin I → ℝ),
    IsPFFluidModelSolution dat Ah Dh Th Zh →
    ∀ t : ℝ, γ * (∑ i, Zh 0 i) ≤ t → Zh t = fun _ => 0

end ProcessingNetworks.ProportionalFairness
