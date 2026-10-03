import Mathlib

namespace ProcessingNetworks.Stability

open MeasureTheory ProbabilityTheory NormedSpace
open scoped NNReal ENNReal

/-- A finite-state marked phase-type representation (Appendix D.9) for a pair `(v, φ)` of a
positive service time `v` and an `I`-dimensional integer-valued output vector `φ`: `v` is the
absorption time of a continuous-time Markov chain on `n` transient phases with sub-generator `T`
and initial phase distribution `α`, and `markProb d i` is the probability that, starting from
phase `i`, absorption eventually carries the mark `d` (`markProb d i ≥ 0` and
`∑ d, markProb d i = 1` for every phase `i`, so `markProb ·` is a genuine mark distribution, not
enforced here since this structure only records the data). The joint survival function is the
standard phase-type formula `P(v > t, φ = d) = αᵀ exp(tT) · markProb d`. -/
structure JointPhaseType (I n : ℕ) where
  T : Matrix (Fin n) (Fin n) ℝ
  markProb : (Fin I → ℕ) → Fin n → ℝ
  α : Fin n → ℝ

/-- `v, φ` are jointly phase-type distributed with representation `pt`, Assumption 2.1(c). -/
def IsJointPhaseType {Ω : Type*} [MeasureSpace Ω] {I n : ℕ} (pt : JointPhaseType I n)
    (v : Ω → ℝ) (φ : Ω → Fin I → ℕ) : Prop :=
  ∀ t : ℝ, 0 ≤ t → ∀ d : Fin I → ℕ,
    (ℙ {ω | t < v ω ∧ φ ω = d}).toReal = pt.α ⬝ᵥ (exp (t • pt.T)).mulVec (pt.markProb d)

/-- `E` is a (homogeneous) Poisson process of rate `lam`: right-continuous (`E 0 = 0`,
nondecreasing) with independent, Poisson-distributed increments over every finite collection of
adjacent time windows. -/
def IsPoissonProcess {Ω : Type*} [MeasureSpace Ω] (E : ℝ → Ω → ℕ) (lam : ℝ≥0) : Prop :=
  (∀ ω, E 0 ω = 0) ∧ (∀ ω, Monotone fun t => E t ω) ∧
  ∀ (n : ℕ) (t : Fin (n + 1) → ℝ), Monotone t → t 0 = 0 →
    iIndepFun (fun i : Fin n => fun ω => E (t i.succ) ω - E (t i.castSucc) ω) ℙ ∧
    ∀ i : Fin n, Measure.map (fun ω => E (t i.succ) ω - E (t i.castSucc) ω) ℙ
      = poissonMeasure (lam * Real.toNNReal (t i.succ - t i.castSucc))

/-- Parts (a)–(c) of Assumption 2.1 (baseline stochastic assumptions), Dai & Harrison, p. 31, for
the core stochastic elements of Section 2.1: `E` collects the `I` external arrival processes
(rates `lam`), which are independent Poisson processes (`poisson` + `arrivals_indep`; when
`lam i = 0` there are no arrivals into buffer `i`); `v, φ` collect, for each activity `j`, the
sequence (indexed by `ℓ : ℕ`, standing for the book's `ℓ = 1, 2, …`) of matched processing-variable
pairs `(vⱼ(ℓ), φⱼ(ℓ))`, i.i.d. with finite means `m j = E[vⱼ(1)] > 0` and `Γ j = E[φⱼ(1)] ≥ 0`
(part (b)) and jointly phase-type distributed (part (c)). -/
structure CoreStochasticAssumptions {Ω : Type*} [MeasureSpace Ω] (I J : ℕ)
    (E : Fin I → ℝ → Ω → ℕ) (lam : Fin I → ℝ≥0)
    (v : Fin J → ℕ → Ω → ℝ) (φ : Fin J → ℕ → Ω → Fin I → ℕ)
    (m : Fin J → ℝ) (Γ : Fin J → Fin I → ℝ) : Prop where
  poisson : ∀ i, IsPoissonProcess (E i) (lam i)
  arrivals_indep :
    iIndep (fun i : Fin I => MeasurableSpace.comap (fun ω => fun t => E i t ω) inferInstance) ℙ
  no_arrival_iff_zero_rate : ∀ i, lam i = 0 → ∀ ω t, E i t ω = 0
  processing_iid : ∀ j, iIndepFun (fun ℓ : ℕ => fun ω => (v j ℓ ω, φ j ℓ ω)) ℙ ∧
      ∀ ℓ, IdentDistrib (fun ω => (v j ℓ ω, φ j ℓ ω)) (fun ω => (v j 0 ω, φ j 0 ω)) ℙ ℙ
  processing_positive : ∀ j ℓ ω, 0 < v j ℓ ω
  mean_service_time : ∀ j, Integrable (v j 0) ℙ ∧ ∫ ω, v j 0 ω ∂ℙ = m j ∧ 0 < m j
  mean_output : ∀ j i, Integrable (fun ω => (φ j 0 ω i : ℝ)) ℙ ∧
      ∫ ω, (φ j 0 ω i : ℝ) ∂ℙ = Γ j i ∧ 0 ≤ Γ j i
  phase_type : ∀ j, ∃ (n : ℕ) (pt : JointPhaseType I n), ∀ ℓ, IsJointPhaseType pt (v j ℓ) (φ j ℓ)

/-- Assumption 2.1 (baseline stochastic assumptions), Dai & Harrison, p. 31, in full: parts
(a)–(c) (`CoreStochasticAssumptions`) together with part (d), the three-way mutual independence of
the initial processing variables `Psi j ℓ` of Eq. (2.3) (only `ℓ < N0 j` is meaningful, matching
`L_{j0}`), the arrival process, and the `J` service-type sequences collectively (the book does not
additionally assert the `J` sequences are independent of one another). -/
structure BaselineAssumptions {Ω : Type*} [MeasureSpace Ω] (I J : ℕ) (N0 : Fin J → ℕ)
    (E : Fin I → ℝ → Ω → ℕ) (lam : Fin I → ℝ≥0)
    (v : Fin J → ℕ → Ω → ℝ) (φ : Fin J → ℕ → Ω → Fin I → ℕ)
    (m : Fin J → ℝ) (Γ : Fin J → Fin I → ℝ)
    (Psi : Fin J → ℕ → Ω → ℝ × (Fin I → ℕ)) : Prop
    extends CoreStochasticAssumptions I J E lam v φ m Γ where
  mutual_independence :
    iIndep (![ MeasurableSpace.comap (fun ω => fun j ℓ => Psi j ℓ ω) inferInstance,
               MeasurableSpace.comap (fun ω => fun i t => E i t ω) inferInstance,
               MeasurableSpace.comap (fun ω => fun j ℓ => (v j ℓ ω, φ j ℓ ω)) inferInstance ]) ℙ

end ProcessingNetworks.Stability
