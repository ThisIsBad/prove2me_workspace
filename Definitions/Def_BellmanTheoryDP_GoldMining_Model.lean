import Mathlib

namespace BellmanTheoryDP.GoldMining

/-- The two gold mines of Bellman's Problem 2: Anaconda (`A`) and Bonanza (`B`). -/
inductive Mine
  | A
  | B
  deriving DecidableEq

/-- A (pure) policy for Problem 2: the mine chosen at use number `n = 0, 1, 2, …`, applied as
long as the machine is undamaged. The only information a policy ever receives is that the
machine is still undamaged, so every history-dependent pure policy is such a sequence. -/
abbrev ChoiceSeq := ℕ → Mine

/-- Number of uses of Anaconda among the first `n` uses (uses `0, …, n-1`). -/
def usesA (σ : ChoiceSeq) (n : ℕ) : ℕ :=
  ((Finset.range n).filter (fun k => σ k = Mine.A)).card

/-- Number of uses of Bonanza among the first `n` uses (uses `0, …, n-1`). -/
def usesB (σ : ChoiceSeq) (n : ℕ) : ℕ :=
  ((Finset.range n).filter (fun k => σ k = Mine.B)).card

/-- Probability that one use of the machine in the given mine succeeds (leaves it undamaged):
`p` in Anaconda, `q` in Bonanza. -/
def successProb (p q : ℝ) : Mine → ℝ
  | Mine.A => p
  | Mine.B => q

/-- Probability that uses `0, 1, …, n` all succeed, i.e. that the gold of use `n` is collected:
`∏_{k ≤ n} (p if σ k = A, q if σ k = B)`. -/
def survival (p q : ℝ) (σ : ChoiceSeq) (n : ℕ) : ℝ :=
  ∏ k ∈ Finset.range (n + 1), successProb p q (σ k)

/-- Gold mined by use number `n` if it succeeds, starting from `x` in Anaconda and `y` in
Bonanza: a fraction `r` of what is left in Anaconda, `r * x * (1 - r) ^ (usesA σ n)`, or a
fraction `s` of what is left in Bonanza, `s * y * (1 - s) ^ (usesB σ n)`. -/
def gain (r s : ℝ) (σ : ChoiceSeq) (x y : ℝ) (n : ℕ) : ℝ :=
  match σ n with
  | Mine.A => r * x * (1 - r) ^ usesA σ n
  | Mine.B => s * y * (1 - s) ^ usesB σ n

/-- Expected amount of gold mined before the machine is damaged, using the choice sequence `σ`
from initial amounts `x` (Anaconda) and `y` (Bonanza):
`J σ x y = ∑_{n ≥ 0} survival n * gain n`. -/
noncomputable def expectedReturn (p q r s : ℝ) (σ : ChoiceSeq) (x y : ℝ) : ℝ :=
  ∑' n : ℕ, survival p q σ n * gain r s σ x y n

/-- Bellman's (8.1): `f(x, y)`, the expected amount of gold mined before the machine is damaged
using an optimal policy, i.e. the supremum of `expectedReturn` over all choice sequences. -/
noncomputable def optimalReturn (p q r s x y : ℝ) : ℝ :=
  ⨆ σ : ChoiceSeq, expectedReturn p q r s σ x y

end BellmanTheoryDP.GoldMining
