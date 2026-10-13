import Mathlib
import Definitions.Def_OnlineStochMatching_TSM_Model

namespace OnlineStochMatching.TSM

open Finset

/-- **Fact 1** (Feldman, Mehta, Mirrokni, Muthukrishnan, *Online Stochastic Matching: Beating
1-1/e*, arXiv:0905.4100v1, §2.1, p. 4; proof App. A, p. 12). Throw `n` balls i.i.d. uniformly into
`n` bins (`balls t` is the bin of ball `t`), fix a set `B` of bins, and let `S` be the number of
bins of `B` that receive at least one ball. For every `ε > 0`, with probability at least
`1 - 2 exp(-ε² n / 2)`,
`|B| (1 - 1/e) - ε n ≤ S ≤ |B| (1 - 1/e + 1/(e n)) + ε n`.

Correction to the page: the statement prints the failure probability as `2 e^{-ε n / 2}`; its own
proof (App. A, p. 12) gives `2 e^{-ε² n / 2}`, and the printed form is false for small `ε` and
large `n`. -/
theorem fact_1 (n : ℕ) (B : Finset (Fin n)) (ε : ℝ) (hε : 0 < ε) :
    1 - 2 * Real.exp (-(ε ^ 2 * n / 2)) ≤
      prob n (fun balls : Fin n → Fin n =>
        (B.card : ℝ) * (1 - 1 / Real.exp 1) - ε * n ≤
            ((B.filter fun b => ∃ t, balls t = b).card : ℝ) ∧
          ((B.filter fun b => ∃ t, balls t = b).card : ℝ) ≤
            (B.card : ℝ) * (1 - 1 / Real.exp 1 + 1 / (Real.exp 1 * n)) + ε * n) := by sorry

end OnlineStochMatching.TSM

