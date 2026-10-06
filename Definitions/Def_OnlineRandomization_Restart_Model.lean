import Mathlib

namespace OnlineRandomization.Restart

/-- p. 7: a request-answer game with real costs. For `r.length = a.length = n`,
`cost r a` is the paper's `f_n(r, a)`; `cost [] []` is `f_0`. Values on lists of
different lengths are never used. -/
structure Game (R A : Type*) where
  cost : List R → List A → ℝ

/-- p. 7: the off-line optimum `c(r) = min { f_n(r, a) | a ∈ A^n }`, a minimum over the
finite nonempty set `A^n`. -/
noncomputable def Game.opt {R A : Type*} [Fintype A] [Nonempty A] (F : Game R A)
    (r : List R) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty (fun a : Fin r.length → A => F.cost r (List.ofFn a))

/-- p. 7: a deterministic online algorithm `(g_i)_{i ≥ 1}`, `g_i : R^i → A`, as one function
on request lists: `G (r_1, …, r_i) = g_i(r_1, …, r_i)`. Only its values on nonempty lists
are used. -/
abbrev DetAlg (R A : Type*) := List R → A

/-- p. 7: `G(r) = (a_1, …, a_n)` with `a_i = g_i(r_1, …, r_i)`. -/
def DetAlg.answers {R A : Type*} (G : DetAlg R A) (r : List R) : List A :=
  (List.range r.length).map fun i => G (r.take (i + 1))

/-- p. 7: the cost of `G` on `r`, `c_G(r) = f_n(r, G(r))`. -/
def DetAlg.costOn {R A : Type*} (F : Game R A) (G : DetAlg R A) (r : List R) : ℝ :=
  F.cost r (G.answers r)

/-- p. 7: a deterministic algorithm is `α`-competitive if `c_G(r) ≤ α(c(r))` for every
request sequence `r`. -/
def IsCompetitive {R A : Type*} [Fintype A] [Nonempty A] (F : Game R A) (α : ℝ → ℝ)
    (G : DetAlg R A) : Prop :=
  ∀ r : List R, G.costOn F r ≤ α (F.opt r)

end OnlineRandomization.Restart
