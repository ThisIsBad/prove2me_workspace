import Mathlib
import Definitions.Def_EdgeDomSets_NPC_Construction

open EdgeDomSets.NPC

theorem GRel_inS_ne (φ : CookLevin.Formula) : ∀ a b : GV φ, GRel φ a b → inS a ≠ inS b := by
    intro a b h
    rcases h with ⟨o, rfl, rfl⟩ | ⟨o, rfl, rfl⟩ | ⟨o, rfl, rfl⟩ | ⟨j, rfl, rfl⟩ |
      ⟨o, o', v, ho, ho', rfl, rfl⟩
    · simp [inS, lit, pend]
    · simp [inS, lit, varNode]
    · unfold clauseNode
      split_ifs with h <;> simp [inS, lit, dNode, dNode', h]
    · simp [inS, dNode, dNode']
    · simp [inS, varNode, ho, ho', isPos]

theorem G_adj_inS_ne (φ : CookLevin.Formula) : ∀ a b : GV φ, (G φ).Adj a b → inS a ≠ inS b := by
    intro a b hab
    rw [G, SimpleGraph.fromRel_adj] at hab
    rcases hab.2 with h | h
    · exact GRel_inS_ne φ a b h
    · exact (GRel_inS_ne φ b a h).symm

theorem G_colorable (φ : CookLevin.Formula) : (G φ).Colorable 2 := by
  refine ⟨SimpleGraph.Coloring.mk (fun v => if inS v then (0 : Fin 2) else 1) ?_⟩
  intro a b hab
  have := G_adj_inS_ne φ a b hab
  cases ha : inS a <;> cases hb : inS b <;> simp_all

theorem solution (φ : CookLevin.Formula) (hφ : IsSat3Restricted φ) :
    (∀ a b : GV φ, (G φ).Adj a b → inS a ≠ inS b) ∧ (G φ).Colorable 2 :=
  ⟨G_adj_inS_ne φ, G_colorable φ⟩
