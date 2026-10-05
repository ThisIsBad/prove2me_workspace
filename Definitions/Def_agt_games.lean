import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Matrix.Basic

/-!
Basic vocabulary of finite strategic-form games, following Nisan–Roughgarden–
Tardos–Vazirani (eds.), *Algorithmic Game Theory* (Cambridge, 2007),
Chapter 1 (Tardos–Vazirani, "Basic Solution Concepts and Computational
Issues", §§1.2–1.3).

A game is presented by a finite type `ι` of players, a finite strategy type
`S i` for each player `i`, and payoff functions `u : ι → (∀ i, S i) → ℝ`,
where `u i s` is the payoff of player `i` when the players jointly play the
pure strategy vector `s` (§1.2).  We use the payoff-maximizing convention
throughout, as the book does outside its cost-based chapters.

Mixed strategies (§1.3.4) are probability distributions on the finite
strategy sets, played independently; they are represented concretely as
weight functions rather than through a measure-theoretic layer, exactly as
the `IsDist` convention of the Markov-chain series.
-/

namespace AGT

open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {S : ι → Type*} [∀ i, Fintype (S i)]

/-- A **lottery** on a finite type: a nonnegative weight for each element,
summing to `1`.  Used for mixed strategies (§1.3.4). -/
def IsLottery {α : Type*} [Fintype α] (p : α → ℝ) : Prop :=
  (∀ a, 0 ≤ p a) ∧ ∑ a, p a = 1

/-- A **mixed-strategy profile**: one lottery per player, the players
randomizing independently (§1.3.4). -/
def IsMixedProfile (σ : ∀ i, S i → ℝ) : Prop :=
  ∀ i, IsLottery (σ i)

/-- The probability that independent draws from the profile `σ` produce the
pure strategy vector `s` (§1.3.4). -/
def profileProb (σ : ∀ i, S i → ℝ) (s : ∀ i, S i) : ℝ :=
  ∏ i, σ i (s i)

/-- Player `i`'s **expected payoff** under the mixed profile `σ`: the
expectation of `u i` over the product distribution induced by `σ` (§1.3.4). -/
def expectedPayoff (u : ι → (∀ i, S i) → ℝ) (σ : ∀ i, S i → ℝ) (i : ι) : ℝ :=
  ∑ s : ∀ j, S j, profileProb σ s * u i s

/-- A pure strategy vector `s` is a **dominant strategy solution** if, for
every player `i` and every strategy vector `t`, playing `s i` against `t`'s
opponents is at least as good for `i` as playing `t i` (§1.3.1). -/
def IsDominantSolution (u : ι → (∀ i, S i) → ℝ) (s : ∀ i, S i) : Prop :=
  ∀ i (t : ∀ j, S j), u i t ≤ u i (Function.update t i (s i))

/-- A pure strategy vector `s` is a **pure Nash equilibrium** if no player
can strictly improve their payoff by a unilateral deviation (§1.3.2). -/
def IsPureNash (u : ι → (∀ i, S i) → ℝ) (s : ∀ i, S i) : Prop :=
  ∀ i (t : S i), u i (Function.update s i t) ≤ u i s

/-- A mixed-strategy profile `σ` is a **mixed Nash equilibrium** if it is a
genuine profile of lotteries and no player can raise their expected payoff by
unilaterally switching to any other lottery over their own strategies
(§1.3.4; the object whose existence is Theorem 1.8). -/
def IsMixedNash (u : ι → (∀ i, S i) → ℝ) (σ : ∀ i, S i → ℝ) : Prop :=
  IsMixedProfile σ ∧
    ∀ i (τ : S i → ℝ), IsLottery τ →
      expectedPayoff u (Function.update σ i τ) i ≤ expectedPayoff u σ i

/-- The strategy family of a **two-player matrix game**: player `true` (the
row player) has strategies `Fin m`, player `false` (the column player) has
strategies `Fin n` (§1.4). -/
def matrixGameStrat (m n : ℕ) : Bool → Type :=
  fun b => bif b then Fin m else Fin n

instance matrixGameStrat.instFintype (m n : ℕ) :
    ∀ b, Fintype (matrixGameStrat m n b) := by
  intro b; cases b <;> dsimp [matrixGameStrat] <;> infer_instance

/-- The payoffs of the **two-person zero-sum game** with payoff matrix `A`
(§1.4): on the pure profile `(x, y)` the row player receives `A x y` and the
column player receives `-A x y` — the payoffs sum to zero, which is the
zero-sum condition. -/
def zeroSumPayoff {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) :
    Bool → (∀ b, matrixGameStrat m n b) → ℝ :=
  fun b s => cond b (A (s true) (s false)) (-(A (s true) (s false)))

/-- The mixed profile of the two-player matrix game in which the row player
plays `p` and the column player plays `q`. -/
def matrixGameProfile {m n : ℕ} (p : Fin m → ℝ) (q : Fin n → ℝ) :
    ∀ b, matrixGameStrat m n b → ℝ :=
  fun b => match b with
    | true => p
    | false => q

end AGT
