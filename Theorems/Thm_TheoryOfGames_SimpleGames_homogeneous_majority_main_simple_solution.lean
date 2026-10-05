import Mathlib
import Definitions.Def_TheoryOfGames_SimpleGames_Majority

namespace TheoryOfGames.SimpleGames

/-- (50:K), p. 444. Let `v` be the characteristic function of a simple game in the reduced form
with `γ = 1` (`v((i)) = -1`), `W^m` its minimal winning coalitions.
1. Every homogeneous weighted majority game possesses a main simple solution: if `w` are weights
   for the game (50:B), (50:1) with common value `a` of the `a_S`, `S` in `W^m` (50:E), then
   `xᵢ = (n / b) wᵢ` with `b = ½ (∑ wᵢ + a)` (50:18) fulfils (50:7), (50:17), and the set of all
   `α^S`, `S` in `W^m`, is a solution.
2. Conversely, if `x` fulfils (50:7) and (50:17) (the game possesses a main simple solution),
   then `wᵢ ≡ xᵢ` are homogeneous weights for the game if and only if (50:20)
   `∑_{i=1}^n xᵢ < 2n`. -/
theorem homogeneous_majority_main_simple_solution {n : ℕ} (v : Finset (Fin n) → ℝ)
    (hv : IsCharFunction v) (hs : IsSimple v) (hred : ∀ i : Fin n, v {i} = -1) :
    (∀ (w : Fin n → ℝ) (a : ℝ), IsWeightsFor v w →
        (∀ S ∈ minimalSets (winningSets v), advantage w S = a) →
        (∀ i, 0 ≤ (n : ℝ) / (((∑ j, w j) + a) / 2) * w i) ∧
        (∀ S ∈ minimalSets (winningSets v),
          ∑ i ∈ S, (n : ℝ) / (((∑ j, w j) + a) / 2) * w i = (n : ℝ)) ∧
        IsSolution v (mainSet (minimalSets (winningSets v))
          (fun i => (n : ℝ) / (((∑ j, w j) + a) / 2) * w i))) ∧
    (∀ x : Fin n → ℝ, (∀ i, 0 ≤ x i) →
        (∀ S ∈ minimalSets (winningSets v), ∑ i ∈ S, x i = (n : ℝ)) →
        ((IsWeightsFor v x ∧ IsHomogeneous x) ↔ ∑ i, x i < 2 * (n : ℝ))) := by sorry

end TheoryOfGames.SimpleGames

