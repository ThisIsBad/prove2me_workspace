import Mathlib
import Definitions.Def_StochasticProg_Recourse_Instance
import Definitions.Def_StochasticProg_IntegerLShaped_Instance

namespace StochasticProg.IntegerLShaped

open StochasticProg.Recourse

variable {n1 n2 m1 m2 K : ℕ}

/-- The algorithm's state: the set of subsets `S` for which an optimality cut (2.1)
has been imposed so far (Integer L-shaped Method, Step 6, p. 293: "impose one
optimality cut (2.1) with `qS = Q(xν)`, set `s = s + 1`"). Steps 0, 1, 3, 4 (the
branch-and-bound bookkeeping around the master, which only affects how fast the search
reaches a cut or a fathom, not whether finiteness holds) are abstracted away, as the
finiteness argument of Proposition 4's proof rests solely on "there are at most `2^n1`
different first-stage solutions" being excluded one at a time by Step 6; see
`MODERATION_NOTES.md` for the scope note. -/
abbrev State (n1 : ℕ) : Type := Finset (Finset (Fin n1))

/-- `(x, θ)` satisfies every optimality cut (2.1) recorded for `Cuts`, with the book's
`qS` value at each recorded `S`. -/
def CutsFeasible (_d : Data n1 n2 m1 m2 K) (Cuts : State n1) (L : ℝ) (qS : Finset (Fin n1) → ℝ)
    (x : Fin n1 → ℝ) (θ : ℝ) : Prop :=
  ∀ S ∈ Cuts, θ ≥ cutRHS L (qS S) S x

/-- `(x, θ)` is a Step-2 optimal solution of the current master problem: a binary,
SIP-feasible `x` minimizing `cᵀx + θ` over all binary SIP-feasible pairs satisfying the
recorded cuts when there are any, `θ` "ignored" (p. 293, Step 0) otherwise — mirroring
`LShaped.IsMasterOptimal`'s treatment of an empty cut set. The relaxation from the
continuous master polytope of Steps 0-4 to optimizing directly over the binary feasible
set is the same abstraction as `State`'s doc-comment: cut (2.1) is proved valid (Prop.
3) for every binary feasible `x'`, so it applies unchanged whether or not a branching
tree is modeled explicitly. -/
def IsBBOptimal (d : Data n1 n2 m1 m2 K) (Cuts : State n1) (L : ℝ) (qS : Finset (Fin n1) → ℝ)
    (x : Fin n1 → ℝ) (θ : ℝ) : Prop :=
  x ∈ K1X d ∧ Binary x ∧
    (Cuts.Nonempty → CutsFeasible d Cuts L qS x θ) ∧
    (if Cuts.Nonempty then
        ∀ x' θ', x' ∈ K1X d → Binary x' → CutsFeasible d Cuts L qS x' θ' →
          dotProduct d.c x + θ ≤ dotProduct d.c x' + θ'
      else
        ∀ x', x' ∈ K1X d → Binary x' → dotProduct d.c x ≤ dotProduct d.c x')

/-- One admissible transition: from a Step-2 optimum `(x, θ)` with `x` the indicator of
a fresh `S`, Step 5 computes `qS S = Q(x)` and Step 6 finds `θ < Q(x)` (not yet
fathomed), so a fresh optimality cut (2.1) is imposed for `S` (p. 293). The case
`θ ≥ Q(x)` (fathom, no cut) is exactly the failure of this relation to hold — it is
read off `¬ Step` at the terminal state in `prop4_integer_lshaped_finite_convergence`. -/
inductive Step (d : Data n1 n2 m1 m2 K) (L : ℝ) (qS : Finset (Fin n1) → ℝ) :
    State n1 → State n1 → Prop
  | cut (Cuts : State n1) (x : Fin n1 → ℝ) (θ : ℝ) (hopt : IsBBOptimal d Cuts L qS x θ)
      (S : Finset (Fin n1)) (hS : x = indicator S) (hnew : S ∉ Cuts)
      (hqS : (qS S : EReal) = QY d x) (hviol : θ < qS S) :
      Step d L qS Cuts (insert S Cuts)

end StochasticProg.IntegerLShaped
