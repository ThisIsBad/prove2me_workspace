import Mathlib
import Definitions.Def_StochasticProg_Recourse_Instance
import Definitions.Def_StochasticProg_IntegerLShaped_Instance
import Definitions.Def_StochasticProg_IntegerLShaped_Algorithm

namespace StochasticProg.IntegerLShaped

open StochasticProg.Recourse

variable {n1 n2 m1 m2 K : ℕ}

/-- Chapter 7, Proposition 4 (p. 293): "Under Assumption 2, the integer L-shaped
method yields an optimal solution of a (SIP) with relatively complete recourse and
first-stage binary variables (when one exists) in a finite number of steps."

`hL` is Assumption 2 (p. 291); `hrcr` is "relatively complete recourse" (Ch. 3, p.
138, `K2 ⊇ K1`, restated for the SIP's `Y`-restricted value in `RelativelyCompleteRecourse`).
The algorithm is the object quantified over via `Step`/`path`: starting from no cuts,
every run reaches, within `N` bounded by the finite total number of possible cut
subsets `Fintype.card (Finset (Fin n1)) = 2^n1` (the proof's "there are at most `2^n1`
different first-stage solutions"), a state `path N` admitting no further `Step`
transition. Termination is then either "no first-stage binary feasible solution
exists" (Step 1, "if none exists, stop") or a binary SIP-feasible point that is
`IsBBOptimal` for the final cut set *and* globally optimal against every binary
SIP-feasible point's true objective `objY` — the "optimal solution ... in a finite
number of steps" the proposition asserts. -/
theorem prop4_integer_lshaped_finite_convergence (d : Data n1 n2 m1 m2 K) (L : ℝ)
    (hL : ∀ x, x ∈ K1X d → Binary x → (L : EReal) ≤ QY d x)
    (hrcr : RelativelyCompleteRecourse d) :
    ∃ (N : ℕ) (qS : Finset (Fin n1) → ℝ) (path : ℕ → State n1),
      N ≤ Fintype.card (Finset (Fin n1)) ∧
      path 0 = ∅ ∧
      (∀ i, i < N → Step d L qS (path i) (path (i + 1))) ∧
      (∀ Cuts', ¬ Step d L qS (path N) Cuts') ∧
      ((∀ x, x ∈ K1X d → ¬ Binary x) ∨
        (∃ x θ, IsBBOptimal d (path N) L qS x θ ∧
          ∀ x', x' ∈ K1X d → Binary x' → objY d x ≤ objY d x')) := by sorry

end StochasticProg.IntegerLShaped
