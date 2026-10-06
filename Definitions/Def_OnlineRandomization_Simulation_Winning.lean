import Definitions.Def_OnlineRandomization_Simulation_Model

namespace OnlineRandomization.Simulation

/-- The request player can force an immediately winning position within
`k` further rounds, including a win at the current position. -/
def WinsWithin {R A : Type*} [Fintype A] [Nonempty A]
    (F : Game R A) (α : ℝ → ℝ) : ℕ → List R → List A → Prop
  | 0, r, a => α (F.opt r) < F.cost r a
  | k + 1, r, a =>
    α (F.opt r) < F.cost r a ∨
      ∃ x : R, ∀ y : A, WinsWithin F α k (r ++ [x]) (a ++ [y])

/-- The paper's winning positions: one finite uniform bound works against
all answer paths. `k = 0` permits an immediate win, including at `([],[])`. -/
def IsWinning {R A : Type*} [Fintype A] [Nonempty A]
    (F : Game R A) (α : ℝ → ℝ) (r : List R) (a : List A) : Prop :=
  ∃ k : ℕ, WinsWithin F α k r a

end OnlineRandomization.Simulation
