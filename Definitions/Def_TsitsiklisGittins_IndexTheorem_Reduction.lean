import Mathlib
import Definitions.Def_TsitsiklisGittins_IndexTheorem_SemiMarkovBandit

namespace TsitsiklisGittins.IndexTheorem

/-- A stage of the index algorithm / of the induction of Tsitsiklis (1994), §2, pp. 196–198,
given by the one-play statistics of every state of `𝒳 = Σ i, X i`:
* `alive` — the states not yet removed;
* `ρ q` — the expected discounted reward of one (composite) play at `q`;
* `w q` — its expected discounted duration `E[∫₀^{T̂(q)} e^{−βt} dt]`;
* `D q p` — the expected discount factor `E[e^{−βT̂(q)}; next state = p]`.
The reward rate of `q` at this stage is `ρ q / w q`. -/
structure Stage (n : ℕ) (X : Fin n → Type) where
  alive : Finset (Σ i, X i)
  ρ : (Σ i, X i) → ℝ
  w : (Σ i, X i) → ℝ
  D : (Σ i, X i) → (Σ i, X i) → ℝ

namespace Stage

variable {n : ℕ} {X : Fin n → Type} [∀ i, Fintype (X i)] [∀ i, DecidableEq (X i)]

/-- The reward rate `ρ q / w q` of the state `q` at this stage: (2.1) at the initial stage,
(2.3) after reductions. -/
noncomputable def rate (S : Stage n X) (q : Σ i, X i) : ℝ := S.ρ q / S.w q

/-- "Reducing bandit `i*` by removing state `s*`" (p. 197), `s = ⟨i*, s*⟩`. A play at `q` that
ends in `s*` is followed by the uninterrupted run of plays at `s*` until a transition to another
state; this composite play has, with `c q = D q s / (1 − D s s)`,
* expected discounted reward `ρ q + c q · ρ s`,
* expected discounted duration `w q + c q · w s`,
* discounted transition data `D q p + c q · D s p` to every `p ≠ s`, and `0` to `s`.
Hence the new rate `(ρ q + c q ρ s) / (w q + c q w s)` is `r̂(q)` of (2.3). For `q` in another
bandit `D q s = 0`, so its data are unchanged. When `s*` is the last alive state of its bandit
this is step (b)'s "remove bandit `i*`". -/
noncomputable def reduce (S : Stage n X) (s : Σ i, X i) : Stage n X where
  alive := S.alive.erase s
  ρ q := S.ρ q + S.D q s / (1 - S.D s s) * S.ρ s
  w q := S.w q + S.D q s / (1 - S.D s s) * S.w s
  D q p := if p = s then 0 else S.D q p + S.D q s / (1 - S.D s s) * S.D s p

/-- The expected discounted reward of the policy `π` from `z` in the problem of this stage. -/
noncomputable def value (S : Stage n X) (π : Policy n X) (z : JointState n X) : ℝ :=
  momentValue S.ρ S.D π z

/-- The stage is the data of a multi-armed bandit problem with discount rate `β`: positive
discounted durations, nonnegative discounted transition data, no transition between bandits,
no transition into a removed state, and `β · w q = 1 − Σ_p D q p` (at the initial stage,
`E[∫₀^T e^{−βt} dt] = (1 − E[e^{−βT}])/β`). -/
def Valid (β : ℝ) (S : Stage n X) : Prop :=
  (∀ q, 0 < S.w q) ∧ (∀ q p, 0 ≤ S.D q p) ∧ (∀ q p, q.1 ≠ p.1 → S.D q p = 0) ∧
    (∀ q p, p ∉ S.alive → S.D q p = 0) ∧ (∀ q, β * S.w q = 1 - ∑ p, S.D q p)

end Stage

namespace SemiMarkovBandit

variable {n : ℕ} {X : Fin n → Type} [∀ i, Fintype (X i)] [∀ i, DecidableEq (X i)]
  [∀ i, MeasurableSpace (X i)] [∀ i, MeasurableSingletonClass (X i)]

/-- The initial stage of the bandit problem `B`: every state alive, `ρ = E[R(x)]`,
`w = E[∫₀^{T(x)} e^{−βt} dt]`, `D = E[e^{−βT(x)}; Y(x) = ·]`; its rate is (2.1). -/
noncomputable def initStage (B : SemiMarkovBandit n X) : Stage n X where
  alive := Finset.univ
  ρ := B.meanReward
  w := B.discDuration
  D := B.discKernel

/-- The stage reached from the initial stage by removing the states of `L`, in order. -/
noncomputable def stageAfter (B : SemiMarkovBandit n X) (L : List (Σ i, X i)) : Stage n X :=
  L.foldl Stage.reduce B.initStage

end SemiMarkovBandit

end TsitsiklisGittins.IndexTheorem
