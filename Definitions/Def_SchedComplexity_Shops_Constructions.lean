import Mathlib
import Definitions.Def_SchedComplexity_Shops_Model

namespace SchedComplexity.Shops

/-! # The four constructions of Theorem 4(g)–(j)

Brucker, Lenstra & Rinnooy Kan, Report BW 43/75, pp. 16–18. The KNAPSACK data are the list
`a = [a_1, …, a_t]` and `b`; `t = a.length` and `A = ∑_{j ∈ T} a_j = a.sum`. Item `j ∈ T` is the job
with 0-based index `j - 1 < t`; the extra jobs `J_{n-1}`, `J_n` are the last indices. Machines
`M_1, M_2, M_3` are `0, 1, 2`. The paper assumes `0 < b < A`, so the natural-number subtraction
`A - b` is the integer one in that range. -/

/-- Theorem 4(i), p. 16: `n = t + 1`; `μ_j = (M_1)`, `p_j1 = a_j` (`j ∈ T`);
`μ_n = (M_2, M_1, M_2)`, `p_n1 = b`, `p_n2 = 1`, `p_n3 = A - b`; no release dates or precedence. -/
def constrI (a : List ℕ) (b : ℕ) : ShopInstance (a.length + 1) 2 where
  ops j := if h : j.val < a.length then [(0, a.get ⟨j.val, h⟩)]
    else [(1, b), (0, 1), (1, a.sum - b)]
  release _ := 0
  prec := ∅

/-- The threshold of Theorem 4(i): `y = A + 1`. -/
def yI (a : List ℕ) : ℕ := a.sum + 1

/-- Theorem 4(j), p. 17: `n = t + 2`; `μ_j = (M_1, M_3)`, `p_j1 = p_j2 = a_j` (`j ∈ T`);
`μ_{n-1} = (M_1, M_2)`, `p_{n-1,1} = b`, `p_{n-1,2} = 2(A - b)`; `μ_n = (M_2, M_3)`,
`p_n1 = 2b`, `p_n2 = A - b`; no release dates or precedence. -/
def constrJ (a : List ℕ) (b : ℕ) : ShopInstance (a.length + 2) 3 where
  ops j := if h : j.val < a.length then [(0, a.get ⟨j.val, h⟩), (2, a.get ⟨j.val, h⟩)]
    else if j.val = a.length then [(0, b), (1, 2 * (a.sum - b))]
    else [(1, 2 * b), (2, a.sum - b)]
  release _ := 0
  prec := ∅

/-- The threshold of Theorem 4(j): `y = 2A`. -/
def yJ (a : List ℕ) : ℕ := 2 * a.sum

/-- Theorem 4(g), p. 18: `n = t + 1`; `r_j = 0`, `p_j1 = t a_j`, `p_j2 = 1` (`j ∈ T`);
`r_n = t b`, `p_n1 = 1`, `p_n2 = t(A - b)`; flow shop (every job visits `M_1` then `M_2`), no
precedence. -/
def constrG (a : List ℕ) (b : ℕ) : ShopInstance (a.length + 1) 2 where
  ops j := if h : j.val < a.length then [(0, a.length * a.get ⟨j.val, h⟩), (1, 1)]
    else [(0, 1), (1, a.length * (a.sum - b))]
  release j := if j.val < a.length then 0 else a.length * b
  prec := ∅

/-- The threshold of Theorem 4(g): `y = t(A + 1)`. -/
def yG (a : List ℕ) : ℕ := a.length * (a.sum + 1)

/-- Theorem 4(h), p. 18: `n = t + 2`; `p_j1 = t a_j`, `p_j2 = 1` (`j ∈ T`);
`p_{n-1,1} = 1`, `p_{n-1,2} = t b`; `p_n1 = 1`, `p_n2 = t(A - b)`; flow shop, all release dates
`0`, and the single precedence arc `J_{n-1} < J_n`. -/
def constrH (a : List ℕ) (b : ℕ) : ShopInstance (a.length + 2) 2 where
  ops j := if h : j.val < a.length then [(0, a.length * a.get ⟨j.val, h⟩), (1, 1)]
    else if j.val = a.length then [(0, 1), (1, a.length * b)]
    else [(0, 1), (1, a.length * (a.sum - b))]
  release _ := 0
  prec := {(⟨a.length, by omega⟩, Fin.last (a.length + 1))}

/-- The threshold of Theorem 4(h): `y = t(A + 1) + 1`. -/
def yH (a : List ℕ) : ℕ := a.length * (a.sum + 1) + 1

end SchedComplexity.Shops
