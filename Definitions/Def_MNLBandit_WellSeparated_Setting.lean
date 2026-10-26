import Mathlib
import Definitions.Def_ChoiceCDLP_MNL_mnlObjective
import Definitions.Def_MNLBandit_LowerBound_Setting
import Definitions.Def_MNLBandit_UCB_Algorithm1
import Definitions.Def_MNLBandit_UCB_Setting

namespace MNLBandit.WellSeparated

open ChoiceCDLP.MNL

/-! ### The MNL model, policies and the history law (§2, pp. 5–7)

Products are `Fin N` (the paper's product `i` is index `i - 1`); a choice outcome is
`Option (Fin N)`, `none` being the no-purchase alternative `0`. The no-purchase weight is
normalized to `v₀ = 1` (p. 5). The choice probabilities (2.1), the feasible family (2.3),
Assumption 4.1.2, `R(S*, v)`, policies, the regret (2.6) and argmax selectors are those of
`MNLBandit.UCB` (module `Def_MNLBandit_UCB_Setting`); the completed-epoch records are
`MNLBandit.UCB.EpochRecord`, and the cardinality family is `MNLBandit.LowerBound.cardFamily`. -/

/-- The expected revenue (2.2), p. 5: `R(S, v) = ∑_{i ∈ S} r_i v_i / (1 + ∑_{j ∈ S} v_j)`,
the published MNL objective with no-purchase weight `1`. -/
noncomputable def revenue {N : ℕ} (v r : Fin N → ℝ) (S : Finset (Fin N)) : ℝ :=
  mnlObjective v r 1 S

/-- The choices of the customers before `t` in a length-`T` history. -/
def histPrefix {N T : ℕ} (h : Fin T → Option (Fin N)) (t : Fin T) : Fin t.val → Option (Fin N) :=
  fun u => h (Fin.castLE t.isLt.le u)

/-- The law of the length-`T` choice history under policy `π`: given the offered sets the choices
are independent with the MNL probabilities (p. 5), so
`ℙ_π(h) = ∏_t p_{h_t}(S_t)` with `S_t = π_t(h_0, …, h_{t-1})`. -/
noncomputable def histProb {N : ℕ} (v : Fin N → ℝ) (π : MNLBandit.UCB.Policy N) (T : ℕ)
    (h : Fin T → Option (Fin N)) : ℝ :=
  ∏ t : Fin T, MNLBandit.UCB.choiceProb v (π t (histPrefix h t)) (h t)

/-- `P_T(E) = ∑_h ℙ_π(h) 𝟙{E h}`, the probability of an event on length-`T` histories. -/
noncomputable def probT {N : ℕ} (v : Fin N → ℝ) (π : MNLBandit.UCB.Policy N) (T : ℕ)
    (E : (Fin T → Option (Fin N)) → Prop) : ℝ := by
  classical
  exact ∑ h : Fin T → Option (Fin N), if E h then histProb v π T h else 0

/-- The cumulative expected revenue (2.5), p. 6: `𝔼_π ∑_{t=1}^T R(S_t, v)`. -/
noncomputable def expectedRevenue {N : ℕ} (v r : Fin N → ℝ) (π : MNLBandit.UCB.Policy N) (T : ℕ) : ℝ :=
  ∑ h : Fin T → Option (Fin N),
    histProb v π T h * ∑ t : Fin T, revenue v r (π t (histPrefix h t))

/-! ### Algorithm 1 (pp. 8–9)

The policy and its state machine are those of `MNLBandit.UCB` (module `Def_MNLBandit_UCB_Algorithm1`):
the upper confidence bound (3.4) is `MNLBandit.UCB.vUCBL`, the optimistic assortment (3.6)–(3.7) is
`MNLBandit.UCB.optimisticSet`, and the state after a sequence of choices is `MNLBandit.UCB.runAlg`. -/

/-- Algorithm 1 as a policy (`MNLBandit.UCB.alg1`): customer `t` is offered the assortment of the
current epoch after the choices of customers `0, …, t - 1`. It uses `N`, `r`, the tie-breaking
selector over `𝒮` and the observed choices only, never `v`. -/
noncomputable abbrev alg1 {N : ℕ} (r : Fin N → ℝ) (sel : (Finset (Fin N) → ℝ) → Finset (Fin N)) :
    MNLBandit.UCB.Policy N :=
  MNLBandit.UCB.alg1 r sel

/-! ### Epochs of a history of Algorithm 1 -/

/-- The epochs completed (closed by a no-purchase) along the history `h`, oldest first, each with
its assortment `S_τ` and purchase counts `v̂_{·,τ}`. -/
noncomputable def completedEpochs {N T : ℕ} (r : Fin N → ℝ)
    (sel : (Finset (Fin N) → ℝ) → Finset (Fin N)) (h : Fin T → Option (Fin N)) :
    List (MNLBandit.UCB.EpochRecord N) :=
  (MNLBandit.UCB.runAlg r sel (List.ofFn h)).past

/-- The number of epochs completed within the first `T` customers. -/
noncomputable def epochsDone {N T : ℕ} (r : Fin N → ℝ)
    (sel : (Finset (Fin N) → ℝ) → Finset (Fin N)) (h : Fin T → Option (Fin N)) : ℕ :=
  (completedEpochs r sel h).length

/-- The number `L` of epochs started within the first `T` customers (p. 8): the completed ones,
plus one if the last customer made a purchase (an epoch in progress). -/
noncomputable def epochsStarted {N T : ℕ} (r : Fin N → ℝ)
    (sel : (Finset (Fin N) → ℝ) → Finset (Fin N)) (h : Fin T → Option (Fin N)) : ℕ :=
  epochsDone r sel h + (match (List.ofFn h).getLast? with
    | some (some _) => 1
    | _ => 0)

/-- `S_ℓ` (1-based `ℓ ≥ 1`): the assortment Algorithm 1 offers in epoch `ℓ` along `h`, computed
from the first `ℓ - 1` completed epochs. Meaningful for `ℓ ≤ epochsDone + 1`. -/
noncomputable def epochSet {N T : ℕ} (r : Fin N → ℝ)
    (sel : (Finset (Fin N) → ℝ) → Finset (Fin N)) (h : Fin T → Option (Fin N)) (ℓ : ℕ) :
    Finset (Fin N) :=
  MNLBandit.UCB.optimisticSet r sel ((completedEpochs r sel h).take (ℓ - 1))

/-- `T_i(ℓ) = |{τ ≤ ℓ | i ∈ S_τ}|` (3.2), along `h`. -/
noncomputable def Tcount {N T : ℕ} (r : Fin N → ℝ)
    (sel : (Finset (Fin N) → ℝ) → Finset (Fin N)) (h : Fin T → Option (Fin N)) (i : Fin N)
    (ℓ : ℕ) : ℕ := by
  classical
  exact ((Finset.Icc 1 ℓ).filter (fun τ => i ∈ epochSet r sel h τ)).card

/-- `v^UCB_{i,ℓ}` (3.4) along `h`: the upper confidence bound computed at the end of epoch `ℓ`
from the first `ℓ` completed epochs (`1` while `T_i(ℓ) = 0`, in particular `v^UCB_{i,0} = 1`).
Meaningful for `ℓ ≤ epochsDone`. -/
noncomputable def vUCB {N T : ℕ} (r : Fin N → ℝ)
    (sel : (Finset (Fin N) → ℝ) → Finset (Fin N)) (h : Fin T → Option (Fin N)) (i : Fin N)
    (ℓ : ℕ) : ℝ :=
  MNLBandit.UCB.vUCBL ((completedEpochs r sel h).take ℓ) i

/-! ### Well-separated instances (§6.1, pp. 19–20) -/

/-- The constant `C₁ = √72 + √24` of Lemma 4.1.2 (value established in its proof, p. 35). -/
noncomputable def C₁ : ℝ := Real.sqrt 72 + Real.sqrt 24

/-- The constant `C₂ = 144` of Lemma 4.1.2 (value established in its proof, p. 35). -/
noncomputable def C₂ : ℝ := 144

/-- The constant `C = max{C₁², C₂}` of (6.2), p. 20. -/
noncomputable def Cmax : ℝ := max (C₁ ^ 2) C₂

/-- The separation `Δ(v)` (6.1), p. 19: `min_{S ∈ 𝒮, R(S, v) ≠ R(S*, v)} (R(S*, v) − R(S, v))`.
If every feasible assortment is optimal (the minimum is over the empty set; the regret is then
`0`), the value is set to `1`. -/
noncomputable def gap {N : ℕ} (v r : Fin N → ℝ) (𝒮 : Finset (Finset (Fin N)))
    (h𝒮 : 𝒮.Nonempty) : ℝ := by
  classical
  exact
    if hne : (𝒮.filter (fun S => revenue v r S ≠ MNLBandit.UCB.optRevenue v r 𝒮 h𝒮)).Nonempty then
      (𝒮.filter (fun S => revenue v r S ≠ MNLBandit.UCB.optRevenue v r 𝒮 h𝒮)).inf' hne
        (fun S => MNLBandit.UCB.optRevenue v r 𝒮 h𝒮 - revenue v r S)
    else 1

/-- `τ = 4 N C log(NT) / Δ²` (6.2), p. 20. -/
noncomputable def tau (N T : ℕ) (Δ : ℝ) : ℝ :=
  4 * N * Cmax * Real.log (N * T) / Δ ^ 2

/-- Epoch `ℓ` is "good" (p. 20) along `h`: for every product `i`,
`0 ≤ v^UCB_{i,ℓ} − v_i ≤ C₁ √(v_i log(√N ℓ + 1) / T_i(ℓ)) + C₂ log(√N ℓ + 1) / T_i(ℓ)`,
the upper inequality required when `T_i(ℓ) ≥ 1`. -/
def IsGood {N T : ℕ} (v r : Fin N → ℝ) (sel : (Finset (Fin N) → ℝ) → Finset (Fin N))
    (h : Fin T → Option (Fin N)) (ℓ : ℕ) : Prop :=
  ∀ i, v i ≤ vUCB r sel h i ℓ ∧
    (1 ≤ Tcount r sel h i ℓ →
      vUCB r sel h i ℓ - v i ≤
        C₁ * Real.sqrt (v i * Real.log (Real.sqrt N * ℓ + 1) / Tcount r sel h i ℓ)
          + C₂ * Real.log (Real.sqrt N * ℓ + 1) / Tcount r sel h i ℓ)

end MNLBandit.WellSeparated
