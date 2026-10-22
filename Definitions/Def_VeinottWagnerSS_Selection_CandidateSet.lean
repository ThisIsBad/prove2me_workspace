import Mathlib
import Definitions.Def_VeinottWagnerSS_Selection_Model

namespace VeinottWagnerSS.Selection

/-- `S̲` ("S underbar", p. 537): the smallest integer that minimizes `G_α`. Under the standing
assumption `G_α(y) → ∞` as `|y| → ∞` the set of minimizers is nonempty and bounded below, so
the infimum is its least element. -/
noncomputable def SLow (M : Model) : ℤ :=
  sInf {y : ℤ | ∀ z : ℤ, M.G y ≤ M.G z}

/-- `S̄` ("S bar", (21), p. 537): the smallest integer not less than `S̲` for which
`G_α(S̄ + 1) ≥ G_α(S̲) + αK`. The set is bounded below by `S̲` and nonempty since
`G_α(y) → ∞` as `y → ∞`. -/
noncomputable def SHigh (M : Model) (α : ℝ) : ℤ :=
  sInf {y : ℤ | SLow M ≤ y ∧ M.G (SLow M) + α * M.K ≤ M.G (y + 1)}

/-- `s̲` ("s underbar", (22), p. 537): the smallest integer for which `G_α(s̲) ≤ G_α(S̲) + K`.
The set contains `S̲` (as `K ≥ 0`) and is bounded below since `G_α(y) → ∞` as `y → −∞`. -/
noncomputable def sLow (M : Model) : ℤ :=
  sInf {y : ℤ | M.G y ≤ M.G (SLow M) + M.K}

/-- `s̄` ("s bar", (23), p. 537): the smallest integer for which
`G_α(s̄) ≤ G_α(S̲) + (1 − α)K`. For `α ≤ 1` the set contains `S̲`, and it is bounded below since
`G_α(y) → ∞` as `y → −∞`. -/
noncomputable def sHigh (M : Model) (α : ℝ) : ℤ :=
  sInf {y : ℤ | M.G y ≤ M.G (SLow M) + (1 - α) * M.K}

/-- `ℒ_α(S, D)` (p. 536): for `x < s = S − D`, `a_α(x | S − D, S)` is a function of `S` and `D`
only; `ℒ_α(S, D)` is that value, taken here at `x = S − D − 1`. -/
noncomputable def calL (M : Model) (α : ℝ) (S D : ℤ) : ℝ :=
  aCost M α (S - D) S (S - D - 1)

/-- The `(s, S)` policies falling within the bounds of Step i (pp. 536–537):
`s̲ ≤ s ≤ s̄`, `S̲ ≤ S ≤ S̄`, and `s ≤ S`. A pair `p` stands for the policy `(s, S) = (p.1, p.2)`. -/
def Box (M : Model) (α : ℝ) : Set (ℤ × ℤ) :=
  {p | sLow M ≤ p.1 ∧ p.1 ≤ sHigh M α ∧ SLow M ≤ p.2 ∧ p.2 ≤ SHigh M α ∧ p.1 ≤ p.2}

/-- The candidate set `𝒮` of Step ii (p. 536): the collection of all `(s, S)` policies within the
bounds of Step i that minimize `ℒ_α(S, D)`, `D = S − s`, over the policies within those bounds. -/
def candSet (M : Model) (α : ℝ) : Set (ℤ × ℤ) :=
  {p | p ∈ Box M α ∧ ∀ q ∈ Box M α, calL M α p.2 (p.2 - p.1) ≤ calL M α q.2 (q.2 - q.1)}

end VeinottWagnerSS.Selection
