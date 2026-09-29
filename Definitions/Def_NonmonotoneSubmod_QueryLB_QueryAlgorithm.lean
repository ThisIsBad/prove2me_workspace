import Mathlib

namespace NonmonotoneSubmod.QueryLB

/-- A deterministic adaptive algorithm that makes `q` value-oracle queries on subsets of `X`
(Feige–Mirrokni–Vondrák 2011, §4.2, p. 1150). `query a` is the next queried set given the list
`a` of oracle answers received so far; `output a` is the returned set given all `q` answers.
Each query may depend on every earlier answer, and answers are arbitrary reals. -/
structure DetAlg (X : Type) (q : ℕ) where
  query : List ℝ → Finset X
  output : List ℝ → Finset X

variable {X : Type} {q : ℕ}

/-- The list of the first `i` oracle answers when `A` runs against the oracle `h`. -/
def DetAlg.answers (A : DetAlg X q) (h : Finset X → ℝ) : ℕ → List ℝ
  | 0 => []
  | i + 1 => A.answers h i ++ [h (A.query (A.answers h i))]

/-- The `i`-th query (`i = 0, …, q − 1`) that `A` issues against the oracle `h`. -/
def DetAlg.queryAt (A : DetAlg X q) (h : Finset X → ℝ) (i : ℕ) : Finset X :=
  A.query (A.answers h i)

/-- The set `A` returns after its `q` queries to the oracle `h`. -/
def DetAlg.run (A : DetAlg X q) (h : Finset X → ℝ) : Finset X :=
  A.output (A.answers h q)

/-- The expected value `E[h(output)]` of a randomized algorithm, modelled as a probability
distribution `μ` over deterministic `q`-query algorithms (its random bits), on the oracle `h`. -/
noncomputable def expectedValue [Fintype X] (μ : PMF (DetAlg X q)) (h : Finset X → ℝ) : ℝ :=
  ∑ S : Finset X, ((μ.map (fun A => A.run h)) S).toReal * h S

end NonmonotoneSubmod.QueryLB
