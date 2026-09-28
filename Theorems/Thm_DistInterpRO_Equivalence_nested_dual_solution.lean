import Mathlib
import Definitions.Def_DistInterpRO_Equivalence_Model

open MeasureTheory

namespace DistInterpRO.Equivalence

theorem nested_dual_solution {m n : ℕ} (f : (Fin m → ℝ) → ℝ) (hf : Measurable f)
    (c : Fin n → ℝ) (hc : ∀ i, 0 < c i) (hsum : ∑ i, c i = 1)
    (Z : Fin n → Set (Fin m → ℝ)) (hZne : ∀ i, (Z i).Nonempty)
    (hZm : ∀ i, MeasurableSet (Z i))
    (hbdd : ∀ i, BddBelow (f '' Z i))
    (hsorted : Antitone (fun i : Fin n => ⨅ x : Z i, f x)) :
    IsDualFeasible Z f (nestedDual (fun i => ⨅ x : Z i, f x)) ∧
      (∀ i : Fin n, ∑ S : Finset (Fin n),
          nestedDual (fun j => ⨅ x : Z j, f x) S * (if i ∈ S then (1 : ℝ) else 0) =
            ⨅ x : Z i, f x) ∧
      ∑ i, c i * ∑ S : Finset (Fin n),
          nestedDual (fun j => ⨅ x : Z j, f x) S * (if i ∈ S then (1 : ℝ) else 0) =
        ∑ i, c i * ⨅ x : Z i, f x := by sorry

end DistInterpRO.Equivalence

