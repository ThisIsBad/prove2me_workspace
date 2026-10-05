import Mathlib
open Filter Topology Matrix

namespace BlackwellDiscreteDP.NearOne

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- A **Markov matrix** (stochastic matrix): nonnegative entries and unit row sums.

Blackwell, Discrete Dynamic Programming, Ann. Math. Statist. 33(2):719–726 (1962),
DOI 10.1214/aoms/1177704593, p. 719, §2 and p. 721, Lemma 1. -/
def IsMarkovMatrix (P : Matrix n n ℝ) : Prop :=
  (∀ i j, 0 ≤ P i j) ∧ ∀ i, ∑ j, P i j = 1

/-- The Cesàro mean `(I + P + ⋯ + P^N)/(N + 1)` of the powers of `P`.

Blackwell (1962), p. 721, Lemma 1(a) (printed "I + Q + ⋯ + Q^N/N + 1", which means
(I + Q + ⋯ + Q^N)/(N + 1)). -/
noncomputable def cesaroMean (P : Matrix n n ℝ) (N : ℕ) : Matrix n n ℝ :=
  ((N : ℝ) + 1)⁻¹ • ∑ k ∈ Finset.range (N + 1), P ^ k

/-- The **limit matrix** `Q*` of a square matrix `P`: the limit, as `N → ∞`, of the Cesàro means
`(I + P + ⋯ + P^N)/(N + 1)`, in the entrywise topology of `Matrix n n ℝ`.

Blackwell (1962), p. 721, Lemma 1(a).

**Formalization Note.** `limUnder` returns an arbitrary matrix when the limit does not exist;
the definition does not presuppose existence. That the Cesàro means of a Markov matrix
converge (so `limitMatrix P` is the true limit) is Lemma 1(a), a theorem. -/
noncomputable def limitMatrix (P : Matrix n n ℝ) : Matrix n n ℝ :=
  limUnder atTop (cesaroMean P)

/-- `H(β) = ∑_{k ≥ 0} β^k (P^k − Q*)`, a matrix-valued function of the discount factor.

Blackwell (1962), p. 721, Lemma 1(d).

**Formalization Note.** A real `tsum` of matrices (entrywise topology); it equals `0` if the
series is not summable. Summability for `0 ≤ β < 1` and a Markov matrix `P` is asserted in the
theorem formalizing Lemma 1(d). -/
noncomputable def deviationSum (P : Matrix n n ℝ) (β : ℝ) : Matrix n n ℝ :=
  ∑' k : ℕ, β ^ k • (P ^ k - limitMatrix P)

/-- `H = (I − P + Q*)⁻¹ − Q*` (the deviation matrix of the chain `P`).

Blackwell (1962), p. 721, Lemma 1(d).

**Formalization Note.** `⁻¹` is Mathlib's total matrix inverse (`0` for a singular matrix);
the nonsingularity of `I − P + Q*` for a Markov matrix `P` is part of the theorem formalizing
Lemma 1(d). -/
noncomputable def deviationMatrix (P : Matrix n n ℝ) : Matrix n n ℝ :=
  (1 - P + limitMatrix P)⁻¹ - limitMatrix P

end BlackwellDiscreteDP.NearOne
