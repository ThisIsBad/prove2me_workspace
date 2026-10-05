import Mathlib
import Definitions.Def_ProcessingNetworks_Stability_BaselineAssumptions

namespace ProcessingNetworks.Subcriticality

open MeasureTheory ProbabilityTheory ProcessingNetworks.Stability

/-- Parts (b)–(d) of Assumption 2.1 (i.i.d. processing variables with finite means, joint
phase-type distribution, and the three-way mutual independence of the initial processing
variables, the arrival process and the processing-variable family), restated verbatim from
mission I's `BaselineAssumptions` without part (a): the processing-variable assumptions that
Sections 4.1–4.2 keep when the arrival process is generalized. -/
structure ProcessingVariableAssumptions {Ω : Type*} [MeasureSpace Ω] (I J : ℕ)
    (E : Fin I → ℝ → Ω → ℕ)
    (v : Fin J → ℕ → Ω → ℝ) (φ : Fin J → ℕ → Ω → Fin I → ℕ)
    (m : Fin J → ℝ) (Γ : Fin J → Fin I → ℝ)
    (Psi : Fin J → ℕ → Ω → ℝ × (Fin I → ℕ)) : Prop where
  processing_iid : ∀ j, iIndepFun (fun ℓ : ℕ => fun ω => (v j ℓ ω, φ j ℓ ω)) ℙ ∧
      ∀ ℓ, IdentDistrib (fun ω => (v j ℓ ω, φ j ℓ ω)) (fun ω => (v j 0 ω, φ j 0 ω)) ℙ ℙ
  processing_positive : ∀ j ℓ ω, 0 < v j ℓ ω
  mean_service_time : ∀ j, Integrable (v j 0) ℙ ∧ ∫ ω, v j 0 ω ∂ℙ = m j ∧ 0 < m j
  mean_output : ∀ j i, Integrable (fun ω => (φ j 0 ω i : ℝ)) ℙ ∧
      ∫ ω, (φ j 0 ω i : ℝ) ∂ℙ = Γ j i ∧ 0 ≤ Γ j i
  phase_type : ∀ j, ∃ (n : ℕ) (pt : JointPhaseType I n), ∀ ℓ, IsJointPhaseType pt (v j ℓ) (φ j ℓ)
  mutual_independence :
    iIndep (![ MeasurableSpace.comap (fun ω => fun j ℓ => Psi j ℓ ω) inferInstance,
               MeasurableSpace.comap (fun ω => fun i t => E i t ω) inferInstance,
               MeasurableSpace.comap (fun ω => fun j ℓ => (v j ℓ ω, φ j ℓ ω)) inferInstance ]) ℙ

/-- Assumption 2.1 weakened to allow a Markovian arrival process (MArP), Corollary 5.4, p. 99
(PDF p. 115): identical to `BaselineAssumptions` except that part (a) (independent Poisson arrival
streams) is replaced by the SLLN conclusion that a MArP is assumed to satisfy (Proposition E.7(a)):
`E i t / t → lam i` almost surely, for a nonnegative rate vector `lam`. Parts (b)-(d) of
Assumption 2.1 (`ProcessingVariableAssumptions`) are unchanged. -/
structure BaselineAssumptionsMArP {Ω : Type*} [MeasureSpace Ω] (I J : ℕ)
    (E : Fin I → ℝ → Ω → ℕ) (lam : Fin I → ℝ)
    (v : Fin J → ℕ → Ω → ℝ) (φ : Fin J → ℕ → Ω → Fin I → ℕ)
    (m : Fin J → ℝ) (Γ : Fin J → Fin I → ℝ)
    (Psi : Fin J → ℕ → Ω → ℝ × (Fin I → ℕ)) : Prop
    extends ProcessingVariableAssumptions I J E v φ m Γ Psi where
  arrival_nonneg : ∀ i, 0 ≤ lam i
  arrival_slln : ℙ {ω | Filter.Tendsto (fun t : ℝ => fun i => (E i t ω : ℝ) / t)
      Filter.atTop (nhds lam)} = 1

end ProcessingNetworks.Subcriticality
