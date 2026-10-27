import Mathlib
import Definitions.Def_FakeUserRanking_FORC_Model
import Definitions.Def_FakeUserRanking_FORC_Algorithm

namespace FakeUserRanking.FORC

open scoped BigOperators

variable {n T : ℕ}

/-- FORC's state at the end of round `t` of trajectory `τ` (after Steps 8–11 of the first `t`
rounds); `t = 0` is the initial state. -/
noncomputable def stateAt
    (tb : List (Fin (numLevels T) × Obs n) → Fin (numLevels T) → Finset (Fin n) → Fin n)
    (fb : List (Fin (numLevels T) × Obs n) → Fin (numLevels T) → Equiv.Perm (Fin n))
    (τ : Fin T → Step n (numLevels T)) (t : ℕ) : State n (numLevels T) :=
  forcState n T tb fb (algHist τ t)

/-- The number of fake users level `k` (paper level `k + 1`) is exposed to over the horizon
(p. 52): rounds whose sampled level is `k` and whose user is fake. -/
def exposure {L : ℕ} (k : Fin L) (τ : Fin T → Step n L) : ℕ :=
  (Finset.univ.filter (fun s : Fin T => (τ s).1 = k ∧ (τ s).2.1.isSome)).card

/-- The window (21), p. 28, extended to `η̂ = 0`:
`w^(ℓ)_{i,t} = √((3/2) log(4nT/δ) / max(η̂^(ℓ)_{i,t}, 1)) + (log(2L/δ) + 4) / max(η̂^(ℓ)_{i,t}, 1)`. -/
noncomputable def window21 (n T : ℕ) {L : ℕ} (st : State n L) (k : Fin L) (i : Fin n) : ℝ :=
  Real.sqrt ((3 / 2) * Real.log (4 * n * T / delta n T) / max (etaHat st k i) 1) +
    (Real.log (2 * L / delta n T) + 4) / max (etaHat st k i) 1

/-- Event `G₂` (Definition 1, p. 29): every level `ℓ ≥ ℓ⋆ = ⌈log₂ F⌉` (Lean: `F ≤ 2^(k+1)`) is
exposed to at most `log(2L/δ) + 3` fake users. -/
noncomputable def goodG2 (F : ℕ) (τ : Fin T → Step n (numLevels T)) : Prop :=
  ∀ k : Fin (numLevels T), F ≤ 2 ^ ((k : ℕ) + 1) →
    (exposure k τ : ℝ) ≤ Real.log (2 * (numLevels T : ℝ) / delta n T) + 3

/-- Event `G₁` (Definition 1, p. 29, with (21)–(22)): at the end of every round `t ∈ [T]`, for
every level `ℓ ≥ ℓ⋆` and every product `i`, `r̂^(ℓ)_{i,t} − w^(ℓ)_{i,t} ≤ μ_i ≤ r̂^(ℓ)_{i,t} + w^(ℓ)_{i,t}`. -/
noncomputable def goodG1 (inst : Instance n) (F : ℕ)
    (tb : List (Fin (numLevels T) × Obs n) → Fin (numLevels T) → Finset (Fin n) → Fin n)
    (fb : List (Fin (numLevels T) × Obs n) → Fin (numLevels T) → Equiv.Perm (Fin n))
    (τ : Fin T → Step n (numLevels T)) : Prop :=
  ∀ t : ℕ, 1 ≤ t → t ≤ T → ∀ k : Fin (numLevels T), F ≤ 2 ^ ((k : ℕ) + 1) → ∀ i : Fin n,
    rHat (stateAt tb fb τ t) k i - window21 n T (stateAt tb fb τ t) k i ≤ inst.μ i ∧
      inst.μ i ≤ rHat (stateAt tb fb τ t) k i + window21 n T (stateAt tb fb τ t) k i

/-- The good event `G = G₁ ∩ G₂` (Definition 1, p. 29). -/
noncomputable def goodEvent (inst : Instance n) (F : ℕ)
    (tb : List (Fin (numLevels T) × Obs n) → Fin (numLevels T) → Finset (Fin n) → Fin n)
    (fb : List (Fin (numLevels T) × Obs n) → Fin (numLevels T) → Equiv.Perm (Fin n))
    (τ : Fin T → Step n (numLevels T)) : Prop :=
  goodG1 inst F tb fb τ ∧ goodG2 F τ

/-- `γ_{j,i} = 64 log(4nT/δ) / Δ²_{j,i}` (23), p. 29. -/
noncomputable def gamma (T : ℕ) (inst : Instance n) (j i : Fin n) : ℝ :=
  64 * Real.log (4 * n * T / delta n T) / gap inst j i ^ 2

end FakeUserRanking.FORC
