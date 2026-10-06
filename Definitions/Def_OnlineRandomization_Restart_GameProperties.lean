import Mathlib
import Definitions.Def_OnlineRandomization_Restart_Model

namespace OnlineRandomization.Restart

/-- p. 16, monotonicity: `f_{n+1}(rt, ab) ≥ f_n(r, a)` for all `r ∈ R^n`, `t ∈ R`,
`a ∈ A^n`, `b ∈ A`. -/
def IsMonotone {R A : Type*} (F : Game R A) : Prop :=
  ∀ (r : List R) (a : List A) (t : R) (b : A), r.length = a.length →
    F.cost r a ≤ F.cost (r ++ [t]) (a ++ [b])

/-- p. 16, locality: for every positive real `h`, only finitely many request sequences
have off-line optimum `c(r) ≤ h`. -/
def IsLocal {R A : Type*} [Fintype A] [Nonempty A] (F : Game R A) : Prop :=
  ∀ h : ℝ, 0 < h → {r : List R | F.opt r ≤ h}.Finite

/-- p. 17: the discrepancy
`δ((r, a), (r', a')) = f(rr', aa') − f(r, a) − f(r', a')`. -/
def discrepancy {R A : Type*} (F : Game R A) (r : List R) (a : List A) (r' : List R)
    (a' : List A) : ℝ :=
  F.cost (r ++ r') (a ++ a') - F.cost r a - F.cost r' a'

/-- p. 17: `D` bounds the diameter of the game, `D(F) = sup |δ((r, a), (r', a'))|` over all
pairs of request-answer sequences of equal lengths, i.e. `D(F) ≤ D`. The game has a finite
diameter iff such a real `D` exists, and `D(F)` is the least one. -/
def DiameterBound {R A : Type*} (F : Game R A) (D : ℝ) : Prop :=
  ∀ (r : List R) (a : List A) (r' : List R) (a' : List A),
    r.length = a.length → r'.length = a'.length → |discrepancy F r a r' a'| ≤ D

end OnlineRandomization.Restart
