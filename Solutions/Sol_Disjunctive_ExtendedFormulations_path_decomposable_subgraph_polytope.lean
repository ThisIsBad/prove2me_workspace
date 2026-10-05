import Mathlib
import Definitions.Def_Disjunctive_ExtendedFormulations_Basic

set_option autoImplicit false

namespace Disjunctive.ExtendedFormulations

def pdA (i j : Fin 3) : Prop := (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 2)

instance : DecidableRel pdA := fun i j => by unfold pdA; infer_instance

lemma pdA_lt {i j : Fin 3} (h : pdA i j) : i < j := by
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide

lemma pdA_acyclic : IsAcyclicDigraph pdA := by
  intro v hv
  have : ∀ a b, Relation.TransGen pdA a b → a < b := by
    intro a b h
    induction h with
    | single h => exact pdA_lt h
    | tail _ h ih => exact lt_trans ih (pdA_lt h)
  exact lt_irrefl _ (this v v hv)

theorem pd_cex_core : ¬ (∀ {V : Type} [Fintype V] [DecidableEq V]
    (A : V → V → Prop) [DecidableRel A] (s t : V) (hst : s ≠ t)
    (hacyclic : IsAcyclicDigraph A),
    PathDecomposableSubgraphPolytope A s t =
      {x : V → ℝ | (∀ i, 0 ≤ x i ∧ x i ≤ 1) ∧ x s = 0 ∧ x t = 0 ∧
        ∀ S : Finset V, s ∉ S → t ∉ S →
          xSum x (S \ GammaStar A s t S) - xSum x (GammaStar A s t S \ S) ≤ 0}) := by
  intro h
  have hEq := h pdA (0 : Fin 3) 2 (by decide) pdA_acyclic
  have hmem : IncidenceVec ({1} : Finset (Fin 3)) ∈ PathDecomposableSubgraphPolytope pdA 0 2 := by
    apply subset_convexHull
    refine ⟨{1}, by decide, by decide, ?_, rfl⟩
    refine ⟨{((0 : Fin 3), (1 : Fin 3)), (1, 2)}, ?_⟩
    decide
  rw [hEq] at hmem
  obtain ⟨_, _, _, hS⟩ := hmem
  have h1 := hS {1} (by decide) (by decide)
  have hG : GammaStar pdA (0 : Fin 3) 2 {1} = {0} := by decide
  rw [hG] at h1
  have e1 : ({1} : Finset (Fin 3)) \ {0} = {1} := by decide
  have e2 : ({0} : Finset (Fin 3)) \ {1} = {0} := by decide
  rw [e1, e2] at h1
  simp [xSum, IncidenceVec] at h1
  linarith

end Disjunctive.ExtendedFormulations

open Disjunctive.ExtendedFormulations

theorem solution : ¬ (∀ {V : Type} [Fintype V] [DecidableEq V]
    (A : V → V → Prop) [DecidableRel A] (s t : V) (hst : s ≠ t)
    (hacyclic : IsAcyclicDigraph A),
    PathDecomposableSubgraphPolytope A s t =
      {x : V → ℝ | (∀ i, 0 ≤ x i ∧ x i ≤ 1) ∧ x s = 0 ∧ x t = 0 ∧
        ∀ S : Finset V, s ∉ S → t ∉ S →
          xSum x (S \ GammaStar A s t S) - xSum x (GammaStar A s t S \ S) ≤ 0}) := by
  exact pd_cex_core
