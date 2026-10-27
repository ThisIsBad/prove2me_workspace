import Mathlib
import Definitions.Def_EdgeDomSets_NPC_Construction

open EdgeDomSets.NPC

theorem count_map_var (c : CookLevin.Clause) (v : ℕ) :
    (c.map CookLevin.Literal.var).count v =
      c.count (CookLevin.Literal.Pos v) + c.count (CookLevin.Literal.Neg v) := by
  induction c with
  | nil => simp
  | cons l c ih =>
    simp only [List.map_cons, List.count_cons, ih]
    cases l with
    | Pos n =>
      by_cases h : n = v
      · subst h; simp [CookLevin.Literal.var]; omega
      · simp [CookLevin.Literal.var, h]
    | Neg n =>
      by_cases h : n = v
      · subst h; simp [CookLevin.Literal.var]; omega
      · simp [CookLevin.Literal.var, h]

theorem count_variablesList (φ : CookLevin.Formula) (v : ℕ) :
    (CookLevin.variablesList φ).count v = posCount φ v + negCount φ v := by
  induction φ with
  | nil => simp [CookLevin.variablesList, posCount, negCount]
  | cons c φ ih =>
    simp only [CookLevin.variablesList, List.foldr_cons, List.count_append] at ih ⊢
    simp only [posCount, negCount, List.map_cons, List.sum_cons] at ih ⊢
    rw [ih, count_map_var]
    ring

theorem length_variablesList (φ : CookLevin.Formula) :
    (CookLevin.variablesList φ).length = (φ.map List.length).sum := by
  induction φ with
  | nil => simp [CookLevin.variablesList]
  | cons c φ ih =>
    simp only [CookLevin.variablesList, List.foldr_cons, List.length_append, List.length_map] at ih ⊢
    rw [ih]; simp

theorem card_Occ (φ : CookLevin.Formula) :
    Fintype.card (Occ φ) = (φ.map List.length).sum := by
  rw [Fintype.card_sigma]
  simp only [Fintype.card_fin]
  rw [← List.sum_ofFn]
  congr 1
  exact List.ofFn_getElem_eq_map φ List.length

theorem card_Occ_eq (φ : CookLevin.Formula) (hφ : IsSat3Restricted φ) :
    Fintype.card (Occ φ) = 3 * numVars φ := by
  rw [card_Occ, ← length_variablesList, ← List.sum_map_count_dedup_eq_length, numVars]
  have : ∀ x ∈ (CookLevin.variablesList φ).dedup, (CookLevin.variablesList φ).count x = 3 := by
    intro x hx
    rw [count_variablesList]
    have := hφ.2 x (List.mem_dedup.mp hx)
    omega
  rw [List.map_congr_left this]
  simp [List.sum_replicate, mul_comm]

/-- the edge chosen at an occurrence -/
noncomputable def edgeOf (φ : CookLevin.Formula) (α : CookLevin.Assignment) (o : Occ φ) :
    Sym2 (GV φ) :=
  if CookLevin.satisfiesLiteral α (occLit o) = true then s(lit o, clauseNode o)
  else s(lit o, varNode o)

theorem assignEdges_eq (φ : CookLevin.Formula) (α : CookLevin.Assignment) :
    assignEdges φ α = by classical exact Finset.univ.image (edgeOf φ α) := by
  unfold assignEdges edgeOf
  rfl

theorem lit_ne_varNode {φ : CookLevin.Formula} (o o' : Occ φ) : lit o ≠ varNode o' := by
  simp [lit, varNode]

theorem lit_ne_clauseNode {φ : CookLevin.Formula} (o o' : Occ φ) : lit o ≠ clauseNode o' := by
  unfold clauseNode; split_ifs <;> simp [lit, dNode, dNode']

theorem lit_injective {φ : CookLevin.Formula} : Function.Injective (lit (φ := φ)) := by
  intro o o' h
  simpa [lit] using h

theorem lit_mem_edgeOf (φ : CookLevin.Formula) (α : CookLevin.Assignment) (o : Occ φ) :
    lit o ∈ edgeOf φ α o := by
  unfold edgeOf; split_ifs <;> exact Sym2.mem_mk_left _ _

theorem edgeOf_injective (φ : CookLevin.Formula) (α : CookLevin.Assignment) :
    Function.Injective (edgeOf φ α) := by
  intro o o' h
  apply lit_injective
  unfold edgeOf at h
  split_ifs at h <;> rw [Sym2.eq_iff] at h <;>
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
    first | exact h1 | exact absurd h1 (lit_ne_clauseNode _ _) | exact absurd h1 (lit_ne_varNode _ _)

theorem edgeOf_mem_edgeSet (φ : CookLevin.Formula) (α : CookLevin.Assignment) (o : Occ φ) :
    edgeOf φ α o ∈ (G φ).edgeSet := by
  unfold edgeOf
  split_ifs with h
  · rw [SimpleGraph.mem_edgeSet, G, SimpleGraph.fromRel_adj]
    exact ⟨lit_ne_clauseNode _ _, Or.inl (Or.inr (Or.inr (Or.inl ⟨o, rfl, rfl⟩)))⟩
  · rw [SimpleGraph.mem_edgeSet, G, SimpleGraph.fromRel_adj]
    exact ⟨lit_ne_varNode _ _, Or.inl (Or.inr (Or.inl ⟨o, rfl, rfl⟩))⟩

theorem clauseNode_mem {φ : CookLevin.Formula} (o : Occ φ) :
    clauseNode o ∈ s(dNode o.1, dNode' o.1) := by
  unfold clauseNode; split_ifs <;> simp

theorem dom_of_GRel (φ : CookLevin.Formula) (α : CookLevin.Assignment)
    (hα : CookLevin.Satisfies α φ) (a b : GV φ) (h : GRel φ a b) :
    ∃ f ∈ (by classical exact Finset.univ.image (edgeOf φ α) : Finset (Sym2 (GV φ))),
      ∃ v, v ∈ s(a, b) ∧ v ∈ f := by
  classical
  rcases h with ⟨o, rfl, rfl⟩ | ⟨o, rfl, rfl⟩ | ⟨o, rfl, rfl⟩ | ⟨j, rfl, rfl⟩ |
      ⟨o, o', v, ho, ho', rfl, rfl⟩
  · exact ⟨edgeOf φ α o, Finset.mem_image_of_mem _ (Finset.mem_univ _), lit o, by simp,
      lit_mem_edgeOf φ α o⟩
  · exact ⟨edgeOf φ α o, Finset.mem_image_of_mem _ (Finset.mem_univ _), lit o, by simp,
      lit_mem_edgeOf φ α o⟩
  · exact ⟨edgeOf φ α o, Finset.mem_image_of_mem _ (Finset.mem_univ _), lit o, by simp,
      lit_mem_edgeOf φ α o⟩
  · have hc := hα (φ.get j) (List.get_mem φ j)
    rw [CookLevin.satisfiesClause_iff] at hc
    obtain ⟨x, hx, hsat⟩ := hc
    obtain ⟨i, hi⟩ := List.mem_iff_get.mp hx
    refine ⟨edgeOf φ α ⟨j, i⟩, Finset.mem_image_of_mem _ (Finset.mem_univ _),
      clauseNode ⟨j, i⟩, clauseNode_mem _, ?_⟩
    have hocc : occLit (⟨j, i⟩ : Occ φ) = x := hi
    unfold edgeOf
    rw [hocc, if_pos hsat]
    exact Sym2.mem_mk_right _ _
  · by_cases hv : α v = true
    · refine ⟨edgeOf φ α o', Finset.mem_image_of_mem _ (Finset.mem_univ _), varNode o',
        by simp, ?_⟩
      unfold edgeOf
      rw [ho', if_neg (by simp [CookLevin.satisfiesLiteral, hv])]
      exact Sym2.mem_mk_right _ _
    · refine ⟨edgeOf φ α o, Finset.mem_image_of_mem _ (Finset.mem_univ _), varNode o,
        by simp, ?_⟩
      unfold edgeOf
      rw [ho, if_neg (by simp [CookLevin.satisfiesLiteral, hv])]
      exact Sym2.mem_mk_right _ _

theorem solution (φ : CookLevin.Formula) (hφ : IsSat3Restricted φ)
    (α : CookLevin.Assignment) (hα : CookLevin.Satisfies α φ) :
    IsEdgeDominating (G φ) (assignEdges φ α) ∧
      (assignEdges φ α).card = 3 * numVars φ := by
  classical
  rw [assignEdges_eq]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro f hf
    obtain ⟨o, -, rfl⟩ := Finset.mem_image.mp hf
    exact edgeOf_mem_edgeSet φ α o
  · intro e he _
    induction e using Sym2.ind with
    | h a b =>
      rw [SimpleGraph.mem_edgeSet, G, SimpleGraph.fromRel_adj] at he
      rcases he.2 with h | h
      · exact dom_of_GRel φ α hα a b h
      · obtain ⟨f, hf, v, hv, hvf⟩ := dom_of_GRel φ α hα b a h
        exact ⟨f, hf, v, by rw [Sym2.eq_swap]; exact hv, hvf⟩
  · rw [Finset.card_image_of_injective _ (edgeOf_injective φ α), Finset.card_univ]
    exact card_Occ_eq φ hφ
