import Mathlib
import Definitions.Def_EdgeDomSets_NPC_Construction

open EdgeDomSets.NPC

instance HAdjDec : DecidableRel H.Adj := fun a b =>
  inferInstanceAs (Decidable (a ≠ b ∧ ((a, b) ∈ HEdges ∨ (b, a) ∈ HEdges)))

theorem eds_of_corner (S : Finset (Fin 3)) (s : Fin 3) (hs : s ∈ S) (D : Finset (Sym2 (Fin 14)))
    (h1 : ∀ f ∈ D, f ∈ H.edgeSet)
    (h2 : ∀ a b : Fin 14, H.Adj a b → s(a, b) ∉ D →
      (∃ f ∈ D, ∃ w, w ∈ s(a, b) ∧ w ∈ f) ∨ attach s ∈ s(a, b)) :
    EdsRestricted S D := by
  refine ⟨h1, ?_⟩
  intro e he hne
  induction e using Sym2.ind with
  | h a b =>
    rw [SimpleGraph.mem_edgeSet] at he
    rcases h2 a b he hne with h | h
    · exact Or.inl h
    · exact Or.inr ⟨s, hs, h⟩

def Dx : Finset (Sym2 (Fin 14)) := {s(ha1, ha2), s(hb2, hb3), s(hy, hc1), s(hv, hc3)}
def Dy : Finset (Sym2 (Fin 14)) := {s(ha1, ha2), s(hb3, hz), s(hc1, hc2), s(hv, hb1)}
def Dz : Finset (Sym2 (Fin 14)) := {s(hx, ha1), s(hb2, hb3), s(hc1, hc2), s(hv, ha3)}

theorem mem_edgeSet_of_adj {a b : Fin 14} (h : H.Adj a b) : s(a, b) ∈ H.edgeSet := h

theorem Dx_sub : ∀ f ∈ Dx, f ∈ H.edgeSet := by
  intro f hf
  simp only [Dx, Finset.mem_insert, Finset.mem_singleton] at hf
  rcases hf with rfl | rfl | rfl | rfl <;> exact mem_edgeSet_of_adj (by decide)

theorem Dy_sub : ∀ f ∈ Dy, f ∈ H.edgeSet := by
  intro f hf
  simp only [Dy, Finset.mem_insert, Finset.mem_singleton] at hf
  rcases hf with rfl | rfl | rfl | rfl <;> exact mem_edgeSet_of_adj (by decide)

theorem Dz_sub : ∀ f ∈ Dz, f ∈ H.edgeSet := by
  intro f hf
  simp only [Dz, Finset.mem_insert, Finset.mem_singleton] at hf
  rcases hf with rfl | rfl | rfl | rfl <;> exact mem_edgeSet_of_adj (by decide)

theorem solution (S : Finset (Fin 3)) (hS : S.Nonempty) :
    ∃ D : Finset (Sym2 (Fin 14)), EdsRestricted S D ∧ D.card = 4 := by
  obtain ⟨s, hs⟩ := hS
  fin_cases s
  · exact ⟨Dx, eds_of_corner S 0 hs Dx Dx_sub (by decide), by decide⟩
  · exact ⟨Dy, eds_of_corner S 1 hs Dy Dy_sub (by decide), by decide⟩
  · exact ⟨Dz, eds_of_corner S 2 hs Dz Dz_sub (by decide), by decide⟩
