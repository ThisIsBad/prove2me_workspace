import Mathlib

namespace OnlineRandomization.Simulation

/-- A real-valued request-answer game. For equal-length lists, `cost r a` is the
paper's `f_n(r,a)`; unequal-length values are unused. -/
structure Game (R A : Type*) where
  cost : List R → List A → ℝ

/-- The best answer string to a fixed request string. -/
noncomputable def Game.opt {R A : Type*} [Fintype A] [Nonempty A]
    (F : Game R A) (r : List R) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty
    (fun a : Fin r.length → A => F.cost r (List.ofFn a))

/-- The paper calls affine cost transformations "linear". -/
def IsLinear (α : ℝ → ℝ) : Prop :=
  ∃ c d : ℝ, ∀ x : ℝ, α x = c * x + d

end OnlineRandomization.Simulation
