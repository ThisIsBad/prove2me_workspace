import Mathlib
import Definitions.Def_BlackwellDiscreteDP_NearOne_LimitMatrix
open Filter Topology Matrix

namespace BlackwellDiscreteDP.NearOne

/-- **Lemma 1(b).** For any `S × S` Markov matrix `Q`, `rank (I − Q) + rank Q* = S`.

Blackwell, Discrete Dynamic Programming, Ann. Math. Statist. 33(2):719–726 (1962),
DOI 10.1214/aoms/1177704593, p. 721, Lemma 1(b).

**Formalization Note.** `S = Fintype.card n`; ranks are `Matrix.rank` over `ℝ`. -/
theorem lemma_1b {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    (Q : Matrix n n ℝ) (hQ : IsMarkovMatrix Q) :
    (1 - Q).rank + (limitMatrix Q).rank = Fintype.card n := by sorry

end BlackwellDiscreteDP.NearOne

