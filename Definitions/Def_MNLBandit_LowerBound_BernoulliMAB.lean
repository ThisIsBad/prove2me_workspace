import Mathlib
import Definitions.Def_MNLBandit_LowerBound_Setting

namespace MNLBandit.LowerBound

/-- The Bernoulli law with parameter `p` on `{0, 1}` (`false ↦ 1 − p`, `true ↦ p`). -/
noncomputable def bern (p : ℝ) : Bool → ℝ
  | true => p
  | false => 1 - p

/-- An online algorithm for the `N`-armed Bernoulli bandit (§5.1, p. 15), possibly randomized:
after the first `t` rounds (arms pulled and 0/1 rewards seen) it pulls arm `i` at round `t`
(0-based) with probability `A t h i`. -/
def MABAlg (N : ℕ) := (t : ℕ) → (Fin t → Fin N × Bool) → Fin N → ℝ

/-- The weights of an online algorithm form a probability vector over arms after every history. -/
def IsMABAlg {N : ℕ} (A : MABAlg N) : Prop :=
  ∀ t (h : Fin t → Fin N × Bool), (∀ i, 0 ≤ A t h i) ∧ ∑ i, A t h i = 1

/-- The law of the length-`T` view `h` (arms pulled and rewards seen) of the algorithm `A` on the
Bernoulli bandit with arm means `μ`. -/
noncomputable def mabLaw {N : ℕ} (A : MABAlg N) (μ : Fin N → ℝ) (T : ℕ)
    (h : Fin T → Fin N × Bool) : ℝ :=
  ∏ t : Fin T, A t (prefixOf h t) (h t).1 * bern (μ (h t).1) (h t).2

/-- The arm means of `I_MAB` (Definition 5.1, p. 15) when the hidden arm is `j`:
`μᵢ = α + ϵ` if `i = j` and `μᵢ = α` otherwise. -/
def imabMeans {N : ℕ} (α ϵ : ℝ) (j : Fin N) : Fin N → ℝ :=
  fun i => if i = j then α + ϵ else α

/-- `ϵ = (1/100) √(N α / T)` of Definition 5.1 (p. 15). -/
noncomputable def epsMAB (N : ℕ) (α : ℝ) (T : ℕ) : ℝ :=
  1 / 100 * Real.sqrt ((N : ℝ) * α / T)

/-- `𝒫_μ(a_{s+1} = i)`: the probability that the arm pulled at time `s + 1` (1-based; after `s`
observed rounds) is `i`, when the arm means are `μ`. -/
noncomputable def armProb {N : ℕ} (A : MABAlg N) (μ : Fin N → ℝ) (s : ℕ) (i : Fin N) : ℝ :=
  ∑ h : Fin s → Fin N × Bool, mabLaw A μ s h * A s h i

/-- The expected regret of `A` on the randomized instance `I_MAB` (Lemma 5.1, p. 15):
`𝔼[∑_{t=1}^T (μ_j − μ_{A_t})]`, the expectation over the hidden arm `j`, uniform on the `N` arms,
and over the rewards and the algorithm's randomization. -/
noncomputable def regretIMAB {N : ℕ} (A : MABAlg N) (α ϵ : ℝ) (T : ℕ) : ℝ :=
  (1 / (N : ℝ)) * ∑ j : Fin N, ∑ h : Fin T → Fin N × Bool,
    mabLaw A (imabMeans α ϵ j) T h * ∑ t : Fin T, (imabMeans α ϵ j j - imabMeans α ϵ j (h t).1)

end MNLBandit.LowerBound
