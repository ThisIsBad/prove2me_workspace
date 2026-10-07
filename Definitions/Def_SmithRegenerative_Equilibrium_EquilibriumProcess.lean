import Mathlib
import Definitions.Def_SmithRegenerative_Equilibrium_Renewal

namespace SmithRegenerative.Equilibrium

open MeasureTheory ProbabilityTheory

variable {Ω : Type*}

/-- The regeneration epochs `T_k = t₀ + t₁ + ⋯ + t_k` (`k = 0, 1, …`) of a general renewal process
(Smith 1955, (2·1·3), p. 9). (`T₋₁ = 0` is not needed separately.) -/
def epoch (t : ℕ → Ω → ℝ) (k : ℕ) (ω : Ω) : ℝ :=
  ∑ i ∈ Finset.range (k + 1), t i ω

/-- The renewal count `n_s` (Smith 1955, §2·1, p. 9): "the greatest integer k such that
`T_{k−1} ≤ s`", i.e. the number of `k ≥ 0` with `T_k ≤ s` (the number of regenerations in `[0, s]`).

Formalization Note: it takes values in `ℕ∞`. It is finite almost surely for a renewal process; on
the null event where infinitely many epochs lie in `[0, s]` it is `⊤`. `0 < n_s` holds exactly
when `t₀ = T₀ ≤ s`. -/
noncomputable def renewalCount (t : ℕ → Ω → ℝ) (s : ℝ) (ω : Ω) : ℕ∞ :=
  {k : ℕ | epoch t k ω ≤ s}.encard

/-- The epoch `L_s` of the **last** regeneration at or before `s`: the largest `T_k ≤ s`, which is
`T_{n_s − 1}` under (2·1·3). The paper writes it `T_{n_t}` in (3·2·1), (3·4·1) and on p. 15 (see the
Formalization Note of `EquilibriumProcess`).

Formalization Note: defined as `⨆ k, (if T_k ≤ s then T_k else 0)`. On `{0 < n_s}` with `n_s`
finite it is `max {T_k : T_k ≤ s}`. On `{n_s = 0}` (that is `t₀ > s`) it is `0` and is never used.
On the null event `n_s = ⊤` it is `sup_k T_k ≤ s`. -/
noncomputable def lastEpoch (t : ℕ → Ω → ℝ) (s : ℝ) (ω : Ω) : ℝ :=
  ⨆ k : ℕ, if epoch t k ω ≤ s then epoch t k ω else 0

/-- **Equilibrium process** `x_t is 𝓔(𝔷, 𝒜, {tᵢ})` (Smith 1955, §3·1–3·4, pp. 12–14, defined by
(3·4·1) on p. 14), with the regeneration event `𝓔` certain (`K_z(+∞) = 1`).

Data.
1. `𝔛` is an abstract measurable space of states; `𝒜` is a class of measurable sets of states (not
   necessarily a σ-algebra).
2. `Z` is the set `𝔷` of boundary (starting) conditions `z`; for each `z`, `P z` is a probability
   measure on one sample space `Ω` (the paper's `P{· | z}`).
3. `t : ℕ → Ω → ℝ` is a general renewal process under every `P z`: `t₀, t₁, t₂, …` are measurable,
   non-negative and independent; `tᵢ` (`i ≥ 1`) has the cycle law `F`, which does not depend on `z`
   ("the tᵢ for i ≥ 1 are independent of z", p. 12); `t₀` has law `K z` (the paper's `K_z(t)`).
4. `x s : Ω → 𝔛` is the state at time `s` (only `s ≥ 0` is used), each measurable.
5. For every `A ∈ 𝒜`, `φ A : ℝ → ℝ` is a measurable function depending only on `A`, not on `z`.

Defining property (3·4·1): `P{x_s ∈ A | z; n_s > 0; L_s} = φ_A(s − L_s)` is a valid representation
of the conditional probability, where `L_s` is the last regeneration epoch at or before `s`. This is
stated as the defining identity of conditional probability: for every `z`, every `A ∈ 𝒜`, every
`s ≥ 0` and every Borel set `B` of epochs,
`P_z{x_s ∈ A, n_s > 0, L_s ∈ B} = ∫_{{n_s > 0, L_s ∈ B}} φ_A(s − L_s) dP_z`,
with `φ_A(s − L_s)` integrable on `{n_s > 0}` (a version of a conditional probability is integrable;
without this the Bochner integral's value `0` for a non-integrable integrand would let a junk `φ_A`
satisfy the identity).

Formalization Note.
* **Index slip.** The paper writes `T_{n_t}` in (3·4·1); under its own (2·1·3) `T_{n_t}` is the first
  regeneration after `t`, while the text means the epoch at which the regeneration "last occurred"
  (p. 13). `lastEpoch` is that epoch, `T_{n_t − 1}`.
* **Certainty is built in.** `t₀` is real-valued, so `K z = law of t₀` is a probability measure:
  `K_z(+∞) = 1`, hypothesis (iii) of Theorem 2. The paper's §3 also allows improper `t₀` (and improper
  `tᵢ`); this structure does not. The cycle law `F` is a proper law, `≠ δ₀` (`IsCycleLaw`).
* The process `x` and the renewal sequence `t` live on the same space and may be dependent; only
  the representation (3·4·1) links them.
* Measurability of `x_s`, of the sets in `𝒜` and of `φ_A` is the standing convention that makes
  `P{x_s ∈ A | …}` and the representation meaningful. The paper lists "`φ_A(t)` is measurable" only
  in Theorem 2 (iv)″_b; its other cases ((iv)′ monotonic, (iv)″_a bounded variation) imply it on
  `(0, ∞)`, and only values on `[0, ∞)` enter (3·4·1). -/
structure EquilibriumProcess (Ω 𝔛 Z : Type*) [MeasurableSpace Ω] [MeasurableSpace 𝔛] where
  /-- `P z` is the probability measure `P{· | z}` for the boundary condition `z`. -/
  P : Z → Measure Ω
  isProb : ∀ z, IsProbabilityMeasure (P z)
  /-- The cycle law `F` of `tᵢ`, `i ≥ 1`. -/
  F : Measure ℝ
  cycleLaw : IsCycleLaw F
  /-- The delay law `K_z` of `t₀` under `P z`. -/
  K : Z → Measure ℝ
  /-- The general renewal process `t₀, t₁, …`. -/
  t : ℕ → Ω → ℝ
  measurable_t : ∀ i, Measurable (t i)
  t_nonneg : ∀ i ω, 0 ≤ t i ω
  indep : ∀ z, iIndepFun t (P z)
  law_cycle : ∀ z (i : ℕ), 1 ≤ i → (P z).map (t i) = F
  law_delay : ∀ z, (P z).map (t 0) = K z
  /-- The state `x_s` at time `s`. -/
  x : ℝ → Ω → 𝔛
  measurable_x : ∀ s, Measurable (x s)
  /-- The class `𝒜` of state sets. -/
  𝒜 : Set (Set 𝔛)
  measurableSet_of_mem : ∀ A ∈ 𝒜, MeasurableSet A
  /-- The functions `φ_A`, depending only on `A`. -/
  φ : Set 𝔛 → ℝ → ℝ
  measurable_φ : ∀ A ∈ 𝒜, Measurable (φ A)
  /-- `φ_A(s − L_s)` is integrable on `{n_s > 0}`, as every version of a conditional probability is
  (part of "a valid representation of the conditional probability" in (3·4·1)). -/
  integrable_repr : ∀ z, ∀ A ∈ 𝒜, ∀ s : ℝ, 0 ≤ s →
    IntegrableOn (fun ω => φ A (s - lastEpoch t s ω)) {ω | 0 < renewalCount t s ω} (P z)
  /-- The representation (3·4·1). -/
  repr : ∀ z, ∀ A ∈ 𝒜, ∀ s : ℝ, 0 ≤ s → ∀ B : Set ℝ, MeasurableSet B →
    (P z {ω | x s ω ∈ A ∧ 0 < renewalCount t s ω ∧ lastEpoch t s ω ∈ B}).toReal =
      ∫ ω in {ω | 0 < renewalCount t s ω ∧ lastEpoch t s ω ∈ B}, φ A (s - lastEpoch t s ω) ∂(P z)

end SmithRegenerative.Equilibrium
