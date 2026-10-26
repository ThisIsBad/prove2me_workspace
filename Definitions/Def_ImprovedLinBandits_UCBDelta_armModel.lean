import Mathlib

namespace ImprovedLinBandits.UCBDelta

/-- `μ_* = max_{1 ≤ i ≤ d} μ_i`, the expected reward of the best arm (Abbasi-Yadkori, Pál,
Szepesvári, NIPS 2011, §6, p. 7). Written as `⨆ i, μ i`, which is the maximum over the finite
type `Fin d` when `0 < d`; every theorem using it assumes `0 < d` (at `d = 0` the value is the
junk `0`). -/
noncomputable def bestMean {d : ℕ} (μ : Fin d → ℝ) : ℝ :=
  ⨆ i, μ i

/-- `Δ_i = μ_* - μ_i`, the gap of arm `i` with respect to the best arm (§6, p. 7). -/
noncomputable def gap {d : ℕ} (μ : Fin d → ℝ) (i : Fin d) : ℝ :=
  bestMean μ - μ i

/-- `N_{i,t}`, the number of rounds among `1, …, t` in which arm `i` was played. Round `s + 1`
plays arm `I (s + 1) ω`; `N_{i,0} = 0`. -/
def pullCount {Ω : Type*} {d : ℕ} (I : ℕ → Ω → Fin d) (i : Fin d) (t : ℕ) (ω : Ω) : ℕ :=
  ((Finset.range t).filter (fun s => I (s + 1) ω = i)).card

/-- `X̄_{i,t}`, the average of the rewards `μ_{I_s} + η_s` received from arm `i` in the rounds
`s ∈ {1, …, t}` with `I_s = i`. When `N_{i,t} = 0` the paper's average is undefined and this
definition returns the junk value `0` (division by zero); every statement using it excludes that
case. -/
noncomputable def empMean {Ω : Type*} {d : ℕ} (μ : Fin d → ℝ) (η : ℕ → Ω → ℝ)
    (I : ℕ → Ω → Fin d) (i : Fin d) (t : ℕ) (ω : Ω) : ℝ :=
  (∑ s ∈ (Finset.range t).filter (fun s => I (s + 1) ω = i), (μ (I (s + 1) ω) + η (s + 1) ω))
    / (pullCount I i t ω : ℝ)

/-- The pseudo-regret `R_n = ∑_{t=1}^n (μ_* - μ_{I_t})` after `n` rounds (§1.2, pp. 2–3, in the
`d`-armed special case of §6, where the decision set is the standard basis). `R_0 = 0`. -/
noncomputable def pseudoRegret {Ω : Type*} {d : ℕ} (μ : Fin d → ℝ) (I : ℕ → Ω → Fin d)
    (n : ℕ) (ω : Ω) : ℝ :=
  ∑ t ∈ Finset.range n, (bestMean μ - μ (I (t + 1) ω))

/-- The confidence width `c_{i,t}` of eq. (3), p. 7, as a function of the pull count
`N = N_{i,t}`:
`√((1 + N) / N² · (1 + 2 log(d (1 + N)^{1/2} / δ)))`.
At `N = 0` the paper's value is `+∞`; here it is the junk value `0` (division by zero), so every
statement using it treats `N = 0` separately. -/
noncomputable def confRadius (d : ℕ) (δ : ℝ) (N : ℕ) : ℝ :=
  Real.sqrt ((1 + (N : ℝ)) / (N : ℝ) ^ 2 *
    (1 + 2 * Real.log ((d : ℝ) * Real.sqrt (1 + (N : ℝ)) / δ)))

end ImprovedLinBandits.UCBDelta
