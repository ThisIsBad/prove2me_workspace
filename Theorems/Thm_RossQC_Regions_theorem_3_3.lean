import Mathlib
import Definitions.Def_RossQC_Regions_Model
import Definitions.Def_RossQC_Regions_TwoState

namespace RossQC.Regions

/-- Ross, *Quality Control under Markovian Deterioration*, Management Science 17(9):587–596 (1971),
DOI 10.1287/mnsc.17.9.587, p. 590, Theorem 3.3: "An optimal policy `R_β` may be determined by three
numbers `P₁, P₂, P₃`, `π ≦ P₁ ≦ P₂ ≦ P₃ ≦ 1`, such that `R_β` produces for `0 ≦ P < P₁`,
inspects for `P₁ ≦ P < P₂`, produces for `P₂ ≦ P < P₃` and revises for `P ≧ P₃`." (The paper
prints "`P₁, P₂, P₂`".)

In the two-state model there are thresholds `π ≤ P₁ ≤ P₂ ≤ P₃` with `P₂ ≤ 1` such that the rule
`fourRegion P₁ P₂ P₃` (produce on `[0, P₁)`, inspect on `[P₁, P₂)`, produce on `[P₂, P₃)`,
revise on `[P₃, 1]`) is β-optimal, and `P₃ ≤ 1` whenever revising is β-optimal at some
`P ∈ [0, 1]`.

**Formalization Note.** The printed bound `P₃ ≦ 1` is false when revising is never optimal (for
instance when `R > C/(1 − β(1 − π))`, where always producing is optimal and revising at `P = 1` is
strictly worse, Theorem 3.4): then no rule revising on a nonempty `[P₃, 1]` is optimal. The
statement therefore keeps `P₃ ≤ 1` exactly when the β-optimal revise region is nonempty, and
otherwise allows `P₃ > 1` (empty revise interval). The rest of the printed chain, `π ≤ P₁ ≤ P₂ ≤ 1`,
is kept unconditionally (inspecting is never optimal at `P = 1`, since `C + βV_β(1) < I + βV_β(1)`).
β-optimality of a rule means it selects a
minimizer of (3) at every `P ∈ [0, 1]` (`IsOptimalRule`). `V_β(P)` is `V2 β π C I R P`, the
general `V_β` of the two-state instance. Standing hypotheses of §3: `0 < β < 1`, `0 ≤ π ≤ 1`,
`C < I < R`, and the implicit `0 < C`. -/
theorem theorem_3_3 (β π C I R : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1) (hπ0 : 0 ≤ π) (hπ1 : π ≤ 1)
    (hC : 0 < C) (hCI : C < I) (hIR : I < R) :
    ∃ P₁ P₂ P₃ : ℝ, π ≤ P₁ ∧ P₁ ≤ P₂ ∧ P₂ ≤ P₃ ∧ P₂ ≤ 1 ∧
      ((region2 β π C I R .revise).Nonempty → P₃ ≤ 1) ∧
      IsOptimalRule β π C I R (fourRegion P₁ P₂ P₃) := by sorry

end RossQC.Regions

