import Mathlib
import Definitions.Def_SmithRegenerative_Equilibrium_EquilibriumProcess

open MeasureTheory ProbabilityTheory

namespace SmithRegenerative.Ergodic

/-- **Renewal process** (Smith, *Regenerative stochastic processes*, Proc. R. Soc. Lond. A
232(1188):6–31 (1955), §2·1, p. 9, unnumbered): "Let {t_i} (i = 1, 2, …) be an infinite sequence
of independent non-negative, identically distributed random variables, which are not zero with
probability one".

Formalization Note: `t : ℕ → Ω → ℝ` is the augmented sequence `t₀, t₁, t₂, …` of the paper; this
structure constrains only the cycle lengths `t 1, t 2, …` (the renewal process proper). The delay
`t 0` is left free here; every theorem of the mission assumes `t₀ = 0` explicitly, as the paper
does in §5. "Random variable" is a measurable real function; "independent" is mutual independence
of `(t (i+1))_{i ≥ 0}` (`iIndepFun`); "identically distributed" is `IdentDistrib (t (i+1)) (t 1)`;
non-negativity holds at every sample point; "not zero with probability one" is
`P {t₁ = 0} < 1`. Strict positivity of the `t_i` is not assumed. -/
structure IsRenewalProcess {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (t : ℕ → Ω → ℝ) :
    Prop where
  measurable : ∀ i, Measurable (t (i + 1))
  indep : iIndepFun (fun i : ℕ => t (i + 1)) P
  identDistrib : ∀ i, IdentDistrib (t (i + 1)) (t 1) P P
  nonneg : ∀ i ω, 0 ≤ t (i + 1) ω
  not_ae_zero : P {ω | t 1 ω = 0} < 1

/-- The counting variable `n_t` (§2·1, p. 9): "the greatest integer k such that T_{k−1} ≤ t".
With `T_{−1} = 0` and non-decreasing epochs this is the number of indices `k ≥ 0` with `T_k ≤ t`,
i.e. the number of regenerations in `[0, t]` counting the one at `T_0`.

Formalization Note: `count t s ω = #{k ≥ 0 : T_k(ω) ≤ s}` via `Set.ncard`. If that set is
infinite (`T_k` bounded, an event of probability zero for a renewal process), `Set.ncard`
returns `0`; this value is a convention on a null event and is never assumed away. -/
noncomputable def count {Ω : Type*} (t : ℕ → Ω → ℝ) (s : ℝ) (ω : Ω) : ℕ :=
  {k : ℕ | SmithRegenerative.Equilibrium.epoch t k ω ≤ s}.ncard

/-- The forward variable `Z_t = Σ_{i=1}^{n_t+1} t_i − t` (§5·2, p. 26). -/
noncomputable def Z {Ω : Type*} (t : ℕ → Ω → ℝ) (s : ℝ) (ω : Ω) : ℝ :=
  (∑ i ∈ Finset.Icc 1 (count t s ω + 1), t i ω) - s

end SmithRegenerative.Ergodic
