import Mathlib
import Definitions.Def_mm_basic
import Definitions.Def_FoundationsML_ReinforcementLearning_IsTransitionKernel
import Definitions.Def_FoundationsML_ReinforcementLearning_IsPolicy
import Definitions.Def_FoundationsML_ReinforcementLearning_InducedReward
import Definitions.Def_FoundationsML_ReinforcementLearning_InducedTransition
import Definitions.Def_FoundationsML_ReinforcementLearning_PolicyValue

namespace AccelVI.AVC

variable {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A]

/-- §2, p. 3: the data (P, r, λ) of an MDP (S, A, P, r, p₀, λ); p₀ is omitted (no planned result uses it). -/
structure MDP (S A : Type*) where
  P : S → A → S → ℝ
  r : S → A → ℝ
  lam : ℝ

/-- §2: every P_ia is a probability distribution over next states (the published
`IsTransitionKernel`), and λ ∈ (0, 1). -/
def MDP.Valid (M : MDP S A) : Prop :=
  FoundationsML.ReinforcementLearning.IsTransitionKernel M.P ∧ 0 < M.lam ∧ M.lam < 1

/-- r_π,i = Σ_a π_ia r_ia (the published `InducedReward`). A policy π ∈ ℝ₊^{n×A} (§2) is the
published predicate `FoundationsML.ReinforcementLearning.IsPolicy`. -/
noncomputable def rPol (M : MDP S A) (pol : S → A → ℝ) : S → ℝ :=
  FoundationsML.ReinforcementLearning.InducedReward pol M.r

/-- L_π,ij = Σ_a π_ia P_iaj (the published `InducedTransition`), as an n × n matrix. -/
noncomputable def LPol (M : MDP S A) (pol : S → A → ℝ) : Matrix S S ℝ :=
  Matrix.of (FoundationsML.ReinforcementLearning.InducedTransition pol M.P)

/-- (2.4): T_π(v) = r_π + λ L_π v. -/
noncomputable def Tpol (M : MDP S A) (pol : S → A → ℝ) (v : S → ℝ) : S → ℝ :=
  rPol M pol + M.lam • (LPol M pol).mulVec v

/-- §2: v^π_i = E^{π,P}[Σ_t λ^t r_{i_t a_t} | i_0 = i] (the published `PolicyValue`, the
discounted series of expected rewards Σ_t λ^t (L_π^t r_π)_i). -/
noncomputable def valuePol (M : MDP S A) (pol : S → A → ℝ) : S → ℝ :=
  FoundationsML.ReinforcementLearning.PolicyValue pol M.P M.r M.lam

/-- κ = (1 + λ)/(1 − λ) (Theorem 5.1). -/
noncomputable def kappa (lam : ℝ) : ℝ := (1 + lam) / (1 - lam)

/-- Definition 2.1, p. 4: the chain with transition matrix `L` is irreducible and admits a
stationary distribution `ν` satisfying the detailed balance equations `ν_i L_ij = ν_j L_ji`
(the stationary distribution is unique by irreducibility). -/
def IsReversible (L : Matrix S S ℝ) : Prop :=
  MarkovMixing.Irreducible L ∧
    ∃ ν : S → ℝ, MarkovMixing.IsStationary L ν ∧ MarkovMixing.DetailedBalance L ν

/-- Algorithm (A-VC), p. 7, with constant step sizes `α`, `γ`: `v₀, v₁` arbitrary and, for
`s ≥ 1`, `h_s = v_s + γ (v_s − v_{s−1})`, `v_{s+1} = h_s − α (h_s − T_π(h_s))`. -/
noncomputable def avc (M : MDP S A) (pol : S → A → ℝ) (α γ : ℝ) (v0 v1 : S → ℝ) : ℕ → (S → ℝ)
  | 0 => v0
  | 1 => v1
  | s + 2 =>
      let h := avc M pol α γ v0 v1 (s + 1) + γ • (avc M pol α γ v0 v1 (s + 1) - avc M pol α γ v0 v1 s)
      h - α • (h - Tpol M pol h)

/-- (4.1), p. 7: α = 1/(1 + λ). -/
noncomputable def alphaAVC (lam : ℝ) : ℝ := 1 / (1 + lam)

/-- (4.1), p. 7: γ = (1 − √(1 − λ²))/λ. -/
noncomputable def gammaAVC (lam : ℝ) : ℝ := (1 - Real.sqrt (1 - lam ^ 2)) / lam

/-- The rate 1 − √(1/κ) of Theorem 5.1 and Lemma 5.3. -/
noncomputable def theta (lam : ℝ) : ℝ := 1 - Real.sqrt (1 / kappa lam)

/-- (5.1), p. 8: the 2n × 2n matrix
`B_π = [[(1 − √(1/κ))(I + L_π), −(1 − √(1/κ))²/2 (I + L_π)], [I, 0]]`. -/
noncomputable def Bpol (M : MDP S A) (pol : S → A → ℝ) : Matrix (S ⊕ S) (S ⊕ S) ℝ :=
  Matrix.fromBlocks (theta M.lam • (1 + LPol M pol)) (-(theta M.lam ^ 2 / 2) • (1 + LPol M pol)) 1 0

/-- Lemma 5.2, p. 8: the stacked vector `x_s = (v_s, v_{s−1}) ∈ ℝ^{2n}` (used for `s ≥ 1`). -/
def xvec (v : ℕ → S → ℝ) (s : ℕ) : S ⊕ S → ℝ := Sum.elim (v s) (v (s - 1))

/-- Lemma 5.2, p. 8: `x^π = (v^π, v^π) ∈ ℝ^{2n}`. -/
noncomputable def xPi (M : MDP S A) (pol : S → A → ℝ) : S ⊕ S → ℝ :=
  Sum.elim (valuePol M pol) (valuePol M pol)

end AccelVI.AVC
