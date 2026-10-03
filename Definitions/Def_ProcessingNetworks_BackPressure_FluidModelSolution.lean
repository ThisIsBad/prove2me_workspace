import Mathlib
import Definitions.Def_ProcessingNetworks_BackPressure_SPNPlanningData
import Definitions.Def_ProcessingNetworks_BackPressure_AllocationPolytope
import Definitions.Def_ProcessingNetworks_BackPressure_RegularPoint

namespace ProcessingNetworks.BackPressure

/-- The fluid equations (6.1)-(6.6), restated at the general-SPN level (index sets `I ≠ J` in
general, unlike missions IV/VI/VII's queueing-network specialization) for arrival-rate vector
`lam`, using `SPNPlanningData`'s own `B`, `Γ`, `m`, `A`, `b`. -/
def IsFluidModelSolution {I J K : ℕ} (dat : SPNPlanningData I J K) (lam : Fin I → ℝ)
    (Dh : ℝ → Fin I → ℝ) (Fh Th : ℝ → Fin J → ℝ) (Zh : ℝ → Fin I → ℝ) : Prop :=
  (∀ t : ℝ, 0 ≤ t → ∀ i, Zh t i = Zh 0 i + lam i * t + ∑ j, dat.Γ i j * Fh t j - Dh t i) ∧
  (∀ t : ℝ, 0 ≤ t → ∀ i, 0 ≤ Zh t i) ∧
  (∀ t : ℝ, 0 ≤ t → ∀ i, Dh t i = ∑ j, dat.B i j * Fh t j) ∧
  (∀ t : ℝ, 0 ≤ t → ∀ j, dat.m j * Fh t j = Th t j) ∧
  (Th 0 = 0 ∧ Monotone Th) ∧
  (∀ s t : ℝ, 0 ≤ s → s ≤ t → ∀ k, ∑ j, dat.A k j * (Th t j - Th s j) ≤ dat.b k * (t - s))

/-- The fluid model corresponding to the relaxed back-pressure control policy: (6.1)-(6.6)
together with the characteristic fluid equation (9.22) (Theorem 9.8) at every regular point. -/
def IsRelaxedBPFluidSolution {I J K : ℕ} (dat : SPNPlanningData I J K) (lam : Fin I → ℝ)
    (Dh : ℝ → Fin I → ℝ) (Fh Th : ℝ → Fin J → ℝ) (Zh : ℝ → Fin I → ℝ) : Prop :=
  IsFluidModelSolution dat lam Dh Fh Th Zh ∧
  ∀ t : ℝ, 0 < t → RegularPoint Dh Fh Th Zh t →
    ∀ d : Fin J → ℝ, HasDerivAt Th d t → IsZMaximal dat d (Zh t)

/-- Definition 6.3 (fluid model stability), specialized to the relaxed back-pressure fluid
model. -/
def RelaxedBPFluidStable {I J K : ℕ} (dat : SPNPlanningData I J K) (lam : Fin I → ℝ) : Prop :=
  ∃ γ : ℝ, 0 < γ ∧ ∀ (Dh : ℝ → Fin I → ℝ) (Fh Th : ℝ → Fin J → ℝ) (Zh : ℝ → Fin I → ℝ),
    IsRelaxedBPFluidSolution dat lam Dh Fh Th Zh →
    ∀ t : ℝ, γ * (∑ i, Zh 0 i) ≤ t → Zh t = fun _ => 0

/-- Uniform convergence on compact sets ("u.o.c."), restated (as in earlier missions) for this
mission's own use. -/
def UOCConverges {d : ℕ} (f : ℕ → ℝ → Fin d → ℝ) (g : ℝ → Fin d → ℝ) : Prop :=
  ∀ T : ℝ, 0 ≤ T → ∀ ε : ℝ, 0 < ε → ∃ Nb : ℕ, ∀ n ≥ Nb, ∀ t ∈ Set.Icc (0 : ℝ) T,
    ∀ i, |f n t i - g t i| < ε

/-- Real-valued u.o.c. convergence, for the scalar time-allocation processes `Y_β`. -/
def UOCConvergesR (f : ℕ → ℝ → ℝ) (g : ℝ → ℝ) : Prop :=
  ∀ T : ℝ, 0 ≤ T → ∀ ε : ℝ, 0 < ε → ∃ Nb : ℕ, ∀ n ≥ Nb, ∀ t ∈ Set.Icc (0 : ℝ) T, |f n t - g t| < ε

end ProcessingNetworks.BackPressure
