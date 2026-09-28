import Mathlib
import Definitions.Def_MonotonicSolutions_CoreRules_Game

namespace MonotonicSolutions.CoreRules

/-- The five coalitions of the proof of Theorem 1 (Young 1985, p. 69), with the paper's
players `1, …, 5` renamed `0, …, 4`:
`S₁ = {3,5}`, `S₂ = {1,2,3}`, `S₃ = {1,3,4}`, `S₄ = {2,4,5}`, `S₅ = {1,2,4,5}`. -/
def youngCoalition : Fin 5 → Finset (Fin 5) :=
  ![{2, 4}, {0, 1, 2}, {0, 2, 3}, {1, 3, 4}, {0, 1, 3, 4}]

/-- The value function of the games of the proof of Theorem 1: `S ↦ top` on the grand
coalition, and otherwise the largest `val k` over the listed coalitions `S_k ⊆ S`
(`0` if `S` contains no `S_k`). -/
def youngMaxFun (val : Fin 5 → ℕ) (top : ℕ) (S : Finset (Fin 5)) : ℝ :=
  if S = Finset.univ then (top : ℝ)
  else (((Finset.univ.filter (fun k => youngCoalition k ⊆ S)).sup val : ℕ) : ℝ)

theorem youngMaxFun_empty (val : Fin 5 → ℕ) (top : ℕ) : youngMaxFun val top ∅ = 0 := by
  unfold youngMaxFun
  have h1 : (∅ : Finset (Fin 5)) ≠ Finset.univ := by decide
  have h2 : Finset.univ.filter (fun k => youngCoalition k ⊆ (∅ : Finset (Fin 5))) = ∅ := by
    decide
  rw [if_neg h1, h2]
  simp

/-- The game built from `youngMaxFun val top`. -/
def youngMaxGame (val : Fin 5 → ℕ) (top : ℕ) : Game 5 :=
  ⟨youngMaxFun val top, youngMaxFun_empty val top⟩

/-- The game `w` of the proof of Theorem 1 (Young 1985, p. 69):
`w(S₁) = w(S₂) = 3`, `w(S₃) = w(S₄) = w(S₅) = 9`, `w(N) = 11`, and otherwise
`w(S) = max_{S_k ⊆ S} w(S_k)` (or `0` if `S` contains no `S_k`). -/
def youngW : Game 5 := youngMaxGame ![3, 3, 9, 9, 9] 11

/-- The game `v` of the proof of Theorem 1 (Young 1985, p. 69): identical to `w` except that
`v(S₅) = v(N) = 12`. -/
def youngV : Game 5 := youngMaxGame ![3, 3, 9, 9, 12] 12

end MonotonicSolutions.CoreRules
