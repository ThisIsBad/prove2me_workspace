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

theorem lit_ne_varNode {φ : CookLevin.Formula} (o o' : Occ φ) : lit o ≠ varNode o' := by
  simp [lit, varNode]

theorem lit_ne_clauseNode {φ : CookLevin.Formula} (o o' : Occ φ) : lit o ≠ clauseNode o' := by
  unfold clauseNode; split_ifs <;> simp [lit, dNode, dNode']

theorem lit_injective {φ : CookLevin.Formula} : Function.Injective (lit (φ := φ)) := by
  intro o o' h
  simpa [lit] using h

/-- in an edge `s(a,b)` with `GRel a b`, a literal vertex can only be `a`. -/
theorem GRel_lit_mem {φ : CookLevin.Formula} {a b : GV φ} (h : GRel φ a b) (o : Occ φ)
    (ho : lit o ∈ s(a, b)) : a = lit o := by
  rw [Sym2.mem_iff] at ho
  rcases ho with rfl | rfl
  · rfl
  · exfalso
    rcases h with ⟨o', rfl, h2⟩ | ⟨o', rfl, h2⟩ | ⟨o', rfl, h2⟩ | ⟨j, h1, h2⟩ |
      ⟨o', o'', v, _, _, h1, h2⟩
    · simp [lit, pend] at h2
    · simp [lit, varNode] at h2
    · exact lit_ne_clauseNode _ _ h2
    · simp [lit, dNode'] at h2
    · simp [lit, varNode] at h2

theorem lits_unique {φ : CookLevin.Formula} {f : Sym2 (GV φ)} (hf : f ∈ (G φ).edgeSet)
    {o o' : Occ φ} (ho : lit o ∈ f) (ho' : lit o' ∈ f) : o = o' := by
  induction f using Sym2.ind with
  | h a b =>
    rw [SimpleGraph.mem_edgeSet, G, SimpleGraph.fromRel_adj] at hf
    rcases hf.2 with h | h
    · exact lit_injective ((GRel_lit_mem h o ho).symm.trans (GRel_lit_mem h o' ho'))
    · rw [Sym2.eq_swap] at ho ho'
      exact lit_injective ((GRel_lit_mem h o ho).symm.trans (GRel_lit_mem h o' ho'))

theorem GRel_pend_mem {φ : CookLevin.Formula} {a b : GV φ} (h : GRel φ a b) (o : Occ φ)
    (ho : pend o ∈ s(a, b)) : s(a, b) = s(lit o, pend o) := by
  rw [Sym2.mem_iff] at ho
  rcases h with ⟨o', rfl, rfl⟩ | ⟨o', rfl, rfl⟩ | ⟨o', rfl, rfl⟩ | ⟨j, rfl, rfl⟩ |
      ⟨o', o'', v, _, _, rfl, rfl⟩
  · rcases ho with h2 | h2
    · simp [lit, pend] at h2
    · have : o = o' := by simpa [pend] using h2
      subst this; rfl
  · rcases ho with h2 | h2
    · simp [lit, pend] at h2
    · simp [pend, varNode] at h2
  · rcases ho with h2 | h2
    · simp [lit, pend] at h2
    · exfalso; revert h2; unfold clauseNode; split_ifs <;> simp [pend, dNode, dNode']
  · rcases ho with h2 | h2
    · simp [pend, dNode] at h2
    · simp [pend, dNode'] at h2
  · rcases ho with h2 | h2
    · simp [pend, varNode] at h2
    · simp [pend, varNode] at h2

theorem pend_edge {φ : CookLevin.Formula} {f : Sym2 (GV φ)} (hf : f ∈ (G φ).edgeSet)
    (o : Occ φ) (ho : pend o ∈ f) : f = s(lit o, pend o) := by
  induction f using Sym2.ind with
  | h a b =>
    rw [SimpleGraph.mem_edgeSet, G, SimpleGraph.fromRel_adj] at hf
    rcases hf.2 with h | h
    · exact GRel_pend_mem h o ho
    · rw [Sym2.eq_swap] at ho ⊢
      exact GRel_pend_mem h o ho

theorem lit_pend_mem_edgeSet {φ : CookLevin.Formula} (o : Occ φ) :
    s(lit o, pend o) ∈ (G φ).edgeSet := by
  rw [SimpleGraph.mem_edgeSet, G, SimpleGraph.fromRel_adj]
  exact ⟨by simp [lit, pend], Or.inl (Or.inl ⟨o, rfl, rfl⟩)⟩

theorem lit_covered {φ : CookLevin.Formula} {F : Finset (Sym2 (GV φ))}
    (hF : IsEdgeDominating (G φ) F) (o : Occ φ) : ∃ f ∈ F, lit o ∈ f := by
  by_cases he : s(lit o, pend o) ∈ F
  · exact ⟨_, he, Sym2.mem_mk_left _ _⟩
  · obtain ⟨f, hf, v, hv, hvf⟩ := hF.2 _ (lit_pend_mem_edgeSet o) he
    rw [Sym2.mem_iff] at hv
    rcases hv with rfl | rfl
    · exact ⟨f, hf, hvf⟩
    · refine ⟨f, hf, ?_⟩
      rw [pend_edge (hF.1 f hf) o hvf]
      exact Sym2.mem_mk_left _ _

theorem card_lower {φ : CookLevin.Formula} (hφ : IsSat3Restricted φ) {F : Finset (Sym2 (GV φ))}
    (hF : IsEdgeDominating (G φ) F) : 3 * numVars φ ≤ F.card := by
  classical
  choose g hg using lit_covered hF
  rw [← card_Occ_eq φ hφ, ← Finset.card_univ]
  refine Finset.card_le_card_of_injOn g (fun o _ => (hg o).1) ?_
  intro o _ o' _ h
  exact lits_unique (hF.1 _ (hg o).1) (hg o).2 (h ▸ (hg o').2)

theorem solution (φ : CookLevin.Formula) (hφ : IsSat3Restricted φ)
    (F : Finset (Sym2 (GV φ))) (hF : IsEdgeDominating (G φ) F) :
    (∀ o : Occ φ, ∃ f ∈ F, lit o ∈ f) ∧ 3 * numVars φ ≤ F.card :=
  ⟨lit_covered hF, card_lower hφ hF⟩
