import Mathlib
import Definitions.Def_Supermodularity_Games_IsEquilibrium
import Definitions.Def_Supermodularity_Games_BestJointResponse

open Supermodularity.Games

/-- The equivalence fails for a game without players: with no players every joint strategy is
vacuously a best joint response to itself, but with an empty feasible set nothing is an
equilibrium. -/
theorem solution : ¬ (∀ {ι : Type} [Fintype ι] [DecidableEq ι] {m : ι → ℕ}
    (S : Set (∀ i, Fin (m i) → ℝ)) (f : ι → (∀ i, Fin (m i) → ℝ) → ℝ)
    (x' : ∀ i, Fin (m i) → ℝ),
    IsEquilibrium S f x' ↔ x' ∈ BestJointResponse S f x') := by
  intro H
  have h := @H PEmpty _ _ (fun _ => 0) ∅ (fun i => PEmpty.elim i) (fun i => PEmpty.elim i)
  have hB : (fun i => PEmpty.elim i : ∀ i : PEmpty, Fin ((fun _ => 0) i) → ℝ) ∈
      BestJointResponse (∅ : Set (∀ i : PEmpty, Fin ((fun _ => 0) i) → ℝ))
        (fun i => PEmpty.elim i) (fun i => PEmpty.elim i) :=
    fun i => PEmpty.elim i
  exact (h.mpr hB).1
