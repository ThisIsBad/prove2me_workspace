import Mathlib

/-!
Hyperplane-query decision trees (Megiddo, J. ACM 31 (1984), §3.1–§3.2, pp. 117–118).

There is an unknown point `x* ∈ ℝ^d` and an oracle that, for any `a ∈ ℝ^d` and `b ∈ ℝ`,
tells whether `aᵀx* < b`, `aᵀx* = b` or `aᵀx* > b`. A search strategy that addresses the
oracle adaptively is a ternary decision tree: each inner node is a hyperplane query
`(a, b)` with one subtree per answer, and each leaf carries a fixed output value. The tree
is built from the data only; the unknown point enters only through `eval`.
-/

namespace MegiddoLP.FixedDim

/-- An adaptive strategy of hyperplane queries in `ℝ^d` with outputs in `α`.
`query a b onLt onEq onGt` asks the oracle for the position of the unknown point `x`
relative to the hyperplane `{y | a ⬝ᵥ y = b}` and continues with `onLt`, `onEq` or `onGt`
according as `a ⬝ᵥ x < b`, `a ⬝ᵥ x = b` or `a ⬝ᵥ x > b`. -/
inductive QTree (d : ℕ) (α : Type) : Type
  | leaf (out : α)
  | query (a : Fin d → ℝ) (b : ℝ) (onLt onEq onGt : QTree d α)

namespace QTree

variable {d : ℕ} {α : Type}

/-- The output of the strategy when the unknown point is `x`: follow the oracle's answers
`compare (a ⬝ᵥ x) b` from the root to a leaf. -/
noncomputable def eval : QTree d α → (Fin d → ℝ) → α
  | leaf out, _ => out
  | query a b onLt onEq onGt, x =>
    match compare (a ⬝ᵥ x) b with
    | .lt => onLt.eval x
    | .eq => onEq.eval x
    | .gt => onGt.eval x

/-- The number of oracle queries the strategy makes when the unknown point is `x`: the
number of query nodes on the root-to-leaf path followed by `x`. -/
noncomputable def numQueries : QTree d α → (Fin d → ℝ) → ℕ
  | leaf _, _ => 0
  | query a b onLt onEq onGt, x =>
    match compare (a ⬝ᵥ x) b with
    | .lt => onLt.numQueries x + 1
    | .eq => onEq.numQueries x + 1
    | .gt => onGt.numQueries x + 1

end QTree

end MegiddoLP.FixedDim
