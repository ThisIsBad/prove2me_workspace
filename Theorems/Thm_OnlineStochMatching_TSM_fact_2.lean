import Mathlib
import Definitions.Def_OnlineStochMatching_TSM_Model

namespace OnlineStochMatching.TSM

open Finset

/-- **Fact 2** (Feldman, Mehta, Mirrokni, Muthukrishnan, *Online Stochastic Matching: Beating
1-1/e*, arXiv:0905.4100v1, §2.1, p. 4; proof App. A, pp. 12–13). Throw `n` balls i.i.d. uniformly
into `n` bins (`balls t` is the bin of ball `t`). Let `B 0, …, B (ℓ-1)` be sequences of `c`
distinct bins each (`B a j` is the `j`-th bin of the `a`-th sequence, positions `0, …, c-1`), with
no bin in more than `d` sequences, and fix a set `R` of positions. Sequence `a` is *satisfied* if
some bin at a position outside `R` has at least one ball, or some bin at a position in `R` has at
least two balls; `S` is the number of satisfied sequences. If `c² < n` and `ε > 0`, then with
probability at least `1 - 2 exp(-ε² n / 2)`,
`S ≥ ℓ (1 - 2^{|R|}/e^c) - ε d n - (2^{|R|} c² / e^c) · ℓ / (n - c²)`.

The hypotheses `c² < n` (so that `n - c² > 0`) and that the bins of each sequence are distinct are
used by the proof (the factor `(1 - c/n)^{n - |R'|}`) without being stated on the page; with
repeated bins the bound fails. -/
theorem fact_2 (n c ℓ d : ℕ) (hcn : c ^ 2 < n) (B : Fin ℓ → Fin c → Fin n)
    (hB : ∀ a, Function.Injective (B a))
    (hd : ∀ b : Fin n, (Finset.univ.filter fun a : Fin ℓ => ∃ j, B a j = b).card ≤ d)
    (R : Finset (Fin c)) (ε : ℝ) (hε : 0 < ε) :
    1 - 2 * Real.exp (-(ε ^ 2 * n / 2)) ≤
      prob n (fun balls : Fin n → Fin n =>
        (ℓ : ℝ) * (1 - 2 ^ R.card / Real.exp 1 ^ c) - ε * d * n
            - (2 ^ R.card * (c : ℝ) ^ 2 / Real.exp 1 ^ c) * ((ℓ : ℝ) / ((n : ℝ) - (c : ℝ) ^ 2)) ≤
          ((Finset.univ.filter fun a : Fin ℓ =>
              (∃ j, j ∉ R ∧ 1 ≤ (Finset.univ.filter fun t => balls t = B a j).card) ∨
              (∃ j, j ∈ R ∧ 2 ≤ (Finset.univ.filter fun t => balls t = B a j).card)).card : ℝ)) := by sorry

end OnlineStochMatching.TSM

