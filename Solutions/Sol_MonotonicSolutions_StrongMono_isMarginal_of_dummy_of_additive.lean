import Mathlib
import Definitions.Def_MonotonicSolutions_StrongMono_Game
import Definitions.Def_MonotonicSolutions_StrongMono_Axioms

namespace MonotonicSolutions.StrongMono

/-- The difference game `v - w`. -/
def aux_imda_sub {n : ℕ} (v w : Game n) : Game n :=
  ⟨fun S => v.1 S - w.1 S, by simp [v.2, w.2]⟩

theorem aux_imda_marginal_sub {n : ℕ} (v w : Game n) (i : Fin n) (S : Finset (Fin n)) :
    marginal (aux_imda_sub v w).1 i S = marginal v.1 i S - marginal w.1 i S := by
  unfold marginal aux_imda_sub
  split_ifs <;> ring

theorem aux_imda_add_sub {n : ℕ} (v w : Game n) : addGame w (aux_imda_sub v w) = v := by
  apply Subtype.ext
  funext S
  simp only [addGame, aux_imda_sub]
  ring

end MonotonicSolutions.StrongMono

open MonotonicSolutions.StrongMono

theorem solution {n : ℕ} (φ : Game n → Fin n → ℝ)
    (hD : SatisfiesDummy φ) (hAdd : IsAdditive φ) : IsMarginal φ := by
  intro v w i h
  have hu : φ (aux_imda_sub v w) i = 0 := by
    apply hD
    intro S
    rw [aux_imda_marginal_sub, h S, sub_self]
  have e := congrFun (hAdd w (aux_imda_sub v w)) i
  rw [aux_imda_add_sub] at e
  rw [e, Pi.add_apply, hu, add_zero]
