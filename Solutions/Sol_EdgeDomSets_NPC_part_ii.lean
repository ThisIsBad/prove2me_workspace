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

theorem count_eq_sum_fin (c : List CookLevin.Literal) (l : CookLevin.Literal) :
    (∑ i : Fin c.length, if c.get i = l then 1 else 0) = c.count l := by
  induction c with
  | nil => simp
  | cons a c ih =>
    rw [List.count_cons, ← ih]
    refine (Fin.sum_univ_succ (fun i : Fin (c.length + 1) =>
      if (a :: c).get i = l then 1 else 0)).trans ?_
    simp only [List.get_cons_zero]
    by_cases h : a = l
    · subst h; simp [add_comm]
    · simp [h]

theorem card_occ_filter (φ : CookLevin.Formula) (l : CookLevin.Literal) :
    (Finset.univ.filter fun o : Occ φ => occLit o = l).card =
      (φ.map fun c => c.count l).sum := by
  rw [Finset.card_filter, Fintype.sum_sigma]
  refine (Finset.sum_congr rfl fun j _ => count_eq_sum_fin (φ.get j) l).trans ?_
  rw [← List.sum_ofFn]
  congr 1
  exact List.ofFn_getElem_eq_map φ (fun c => c.count l)

theorem neg_occ_unique {φ : CookLevin.Formula} (hφ : IsSat3Restricted φ) (v : ℕ)
    (hv : v ∈ CookLevin.variablesList φ) :
    ∃ o : Occ φ, occLit o = .Neg v ∧ ∀ o', occLit o' = .Neg v → o' = o := by
  classical
  have h := (hφ.2 v hv).2
  have h1 : (Finset.univ.filter fun o : Occ φ => occLit o = .Neg v).card = 1 := by
    rw [card_occ_filter]; exact h
  obtain ⟨a, ha⟩ := Finset.card_eq_one.mp h1
  have hmem : ∀ o, occLit o = .Neg v ↔ o ∈ ({a} : Finset _) := by
    intro o; rw [← ha]; simp
  exact ⟨a, (hmem a).mpr (Finset.mem_singleton_self a),
    fun o' ho' => Finset.mem_singleton.mp ((hmem o').mp ho')⟩

theorem var_mem_variablesList {φ : CookLevin.Formula} (o : Occ φ) :
    (occLit o).var ∈ CookLevin.variablesList φ := by
  rw [CookLevin.mem_variablesList_iff]
  exact ⟨φ.get o.1, List.get_mem _ _, occLit o, List.get_mem _ _, rfl⟩

theorem GRel_lit_d {φ : CookLevin.Formula} {a b : GV φ} (h : GRel φ a b) (o : Occ φ)
    (ho : lit o ∈ s(a, b)) (j : Fin φ.length) (hj : dNode j ∈ s(a, b) ∨ dNode' j ∈ s(a, b)) :
    s(a, b) = s(lit o, clauseNode o) ∧ o.1 = j := by
  have ha := GRel_lit_mem h o ho
  subst ha
  rcases h with ⟨o', ho', rfl⟩ | ⟨o', ho', rfl⟩ | ⟨o', ho', rfl⟩ | ⟨j', h1, h2⟩ |
      ⟨o', o'', v, _, _, h1, h2⟩
  · exfalso; simp [lit, pend, dNode, dNode', Sym2.mem_iff] at hj
  · exfalso; simp [lit, varNode, dNode, dNode', Sym2.mem_iff] at hj
  · have : o = o' := lit_injective ho'
    subst this
    refine ⟨rfl, ?_⟩
    revert hj; unfold clauseNode; split_ifs <;> simp [lit, dNode, dNode', Sym2.mem_iff] <;>
      intro h <;> exact h.symm
  · simp [lit, dNode] at h1
  · simp [lit, varNode] at h1

theorem lit_d_edge {φ : CookLevin.Formula} {f : Sym2 (GV φ)} (hf : f ∈ (G φ).edgeSet)
    (o : Occ φ) (ho : lit o ∈ f) (j : Fin φ.length) (hj : dNode j ∈ f ∨ dNode' j ∈ f) :
    f = s(lit o, clauseNode o) ∧ o.1 = j := by
  induction f using Sym2.ind with
  | h a b =>
    rw [SimpleGraph.mem_edgeSet, G, SimpleGraph.fromRel_adj] at hf
    rcases hf.2 with h | h
    · exact GRel_lit_d h o ho j hj
    · rw [Sym2.eq_swap] at ho hj ⊢
      exact GRel_lit_d h o ho j hj

theorem GRel_lit_var {φ : CookLevin.Formula} {a b : GV φ} (h : GRel φ a b) (o o' : Occ φ)
    (ho : lit o ∈ s(a, b)) (ho' : varNode o' ∈ s(a, b)) :
    o = o' ∧ s(a, b) = s(lit o, varNode o) := by
  have ha := GRel_lit_mem h o ho
  subst ha
  rcases h with ⟨o₁, ho₁, rfl⟩ | ⟨o₁, ho₁, rfl⟩ | ⟨o₁, ho₁, rfl⟩ | ⟨j', h1, h2⟩ |
      ⟨o₁, o₂, v, _, _, h1, h2⟩
  · exfalso; simp [lit, pend, varNode, Sym2.mem_iff] at ho'
  · have : o = o₁ := lit_injective ho₁
    subst this
    simp [lit, varNode, Sym2.mem_iff] at ho'
    subst ho'
    exact ⟨rfl, rfl⟩
  · exfalso; revert ho'; unfold clauseNode; split_ifs <;> simp [lit, varNode, dNode, dNode', Sym2.mem_iff]
  · simp [lit, dNode] at h1
  · simp [lit, varNode] at h1

theorem lit_var_edge {φ : CookLevin.Formula} {f : Sym2 (GV φ)} (hf : f ∈ (G φ).edgeSet)
    (o o' : Occ φ) (ho : lit o ∈ f) (ho' : varNode o' ∈ f) :
    o = o' ∧ f = s(lit o, varNode o) := by
  induction f using Sym2.ind with
  | h a b =>
    rw [SimpleGraph.mem_edgeSet, G, SimpleGraph.fromRel_adj] at hf
    rcases hf.2 with h | h
    · exact GRel_lit_var h o o' ho ho'
    · rw [Sym2.eq_swap] at ho ho' ⊢
      exact GRel_lit_var h o o' ho ho'

theorem clauseNode_ne_varNode {φ : CookLevin.Formula} (o o' : Occ φ) :
    clauseNode o ≠ varNode o' := by
  unfold clauseNode; split_ifs <;> simp [dNode, dNode', varNode]

theorem dd_mem_edgeSet {φ : CookLevin.Formula} (j : Fin φ.length) :
    s(dNode j, dNode' j) ∈ (G φ).edgeSet := by
  rw [SimpleGraph.mem_edgeSet, G, SimpleGraph.fromRel_adj]
  exact ⟨by simp [dNode, dNode'], Or.inl (Or.inr (Or.inr (Or.inr (Or.inl ⟨j, rfl, rfl⟩))))⟩

theorem vv_mem_edgeSet {φ : CookLevin.Formula} (o o' : Occ φ) (v : ℕ)
    (ho : occLit o = .Pos v) (ho' : occLit o' = .Neg v) :
    s(varNode o, varNode o') ∈ (G φ).edgeSet := by
  rw [SimpleGraph.mem_edgeSet, G, SimpleGraph.fromRel_adj]
  refine ⟨?_, Or.inl (Or.inr (Or.inr (Or.inr (Or.inr ⟨o, o', v, ho, ho', rfl, rfl⟩))))⟩
  intro h
  have : o = o' := by simpa [varNode] using h
  subst this
  rw [ho] at ho'
  cases ho'

theorem solution (φ : CookLevin.Formula) (hφ : IsSat3Restricted φ)
    (F : Finset (Sym2 (GV φ))) (hF : IsEdgeDominating (G φ) F)
    (hcard : F.card = 3 * numVars φ) :
    CookLevin.Satisfies (assignOfEdges φ F) φ := by
  classical
  choose g hg using lit_covered hF
  have ginj : Function.Injective g := fun o o' h =>
    lits_unique (hF.1 _ (hg o).1) (hg o).2 (h ▸ (hg o').2)
  have hFeq : F = Finset.univ.image g := by
    symm
    apply Finset.eq_of_subset_of_card_le
    · intro f hf
      obtain ⟨o, -, rfl⟩ := Finset.mem_image.mp hf
      exact (hg o).1
    · rw [Finset.card_image_of_injective _ ginj, Finset.card_univ, card_Occ_eq φ hφ, hcard]
  have hlit : ∀ f ∈ F, ∃ o, f = g o := by
    intro f hf
    rw [hFeq] at hf
    obtain ⟨o, -, rfl⟩ := Finset.mem_image.mp hf
    exact ⟨o, rfl⟩
  have huniq : ∀ o, ∀ f ∈ F, lit o ∈ f → f = g o := by
    intro o f hf ho
    obtain ⟨o', rfl⟩ := hlit f hf
    rw [lits_unique (hF.1 _ hf) ho (hg o').2]
  intro c hc
  obtain ⟨j, rfl⟩ := List.mem_iff_get.mp hc
  rw [CookLevin.satisfiesClause_iff]
  have hnot : s(dNode j, dNode' j) ∉ F := by
    intro hmem
    obtain ⟨o, ho⟩ := hlit _ hmem
    have := (hg o).2
    rw [← ho] at this
    simp [lit, dNode, dNode', Sym2.mem_iff] at this
  obtain ⟨f, hf, w, hw, hwf⟩ := hF.2 _ (dd_mem_edgeSet j) hnot
  obtain ⟨o, rfl⟩ := hlit f hf
  have hw' : dNode j ∈ g o ∨ dNode' j ∈ g o := by
    rw [Sym2.mem_iff] at hw
    rcases hw with rfl | rfl
    · exact Or.inl hwf
    · exact Or.inr hwf
  obtain ⟨hgo, hoj⟩ := lit_d_edge (hF.1 _ hf) o (hg o).2 j hw'
  obtain ⟨j', i⟩ := o
  simp only at hoj
  subst hoj
  refine ⟨occLit ⟨j', i⟩, List.get_mem _ _, ?_⟩
  -- the unique edge of `F` at `lit o` is not the variable-side edge
  have hnotvar : s(lit ⟨j', i⟩, varNode ⟨j', i⟩) ∉ F := by
    intro hmem
    have h1 := huniq _ _ hmem (Sym2.mem_mk_left _ _)
    rw [hgo, Sym2.eq_iff] at h1
    rcases h1 with ⟨-, h2⟩ | ⟨h2, -⟩
    · exact clauseNode_ne_varNode _ _ h2.symm
    · exact lit_ne_clauseNode _ _ h2
  cases hl : occLit ⟨j', i⟩ with
  | Pos v =>
    simp only [CookLevin.satisfiesLiteral]
    unfold assignOfEdges
    simp only [decide_eq_true_iff]
    have hv : v ∈ CookLevin.variablesList φ := by
      have := var_mem_variablesList (⟨j', i⟩ : Occ φ)
      rwa [hl] at this
    obtain ⟨o', ho', -⟩ := neg_occ_unique hφ v hv
    refine ⟨o', ho', ?_⟩
    have hnotvv : s(varNode ⟨j', i⟩, varNode o') ∉ F := by
      intro hmem
      obtain ⟨o'', ho''⟩ := hlit _ hmem
      have := (hg o'').2
      rw [← ho''] at this
      simp [lit, varNode, Sym2.mem_iff] at this
    obtain ⟨f', hf', w', hw', hw'f⟩ := hF.2 _ (vv_mem_edgeSet _ o' v hl ho') hnotvv
    obtain ⟨o'', rfl⟩ := hlit f' hf'
    rw [Sym2.mem_iff] at hw'
    rcases hw' with rfl | rfl
    · exfalso
      obtain ⟨rfl, h2⟩ := lit_var_edge (hF.1 _ hf') o'' _ (hg o'').2 hw'f
      rw [h2] at hf'
      exact hnotvar hf'
    · obtain ⟨rfl, h2⟩ := lit_var_edge (hF.1 _ hf') o'' _ (hg o'').2 hw'f
      rw [h2] at hf'
      exact hf'
  | Neg v =>
    simp only [CookLevin.satisfiesLiteral]
    unfold assignOfEdges
    simp only [Bool.not_eq_true', decide_eq_false_iff_not]
    rintro ⟨o', ho', hmem⟩
    have hv : v ∈ CookLevin.variablesList φ := by
      have := var_mem_variablesList (⟨j', i⟩ : Occ φ)
      rwa [hl] at this
    obtain ⟨o₀, -, huniq'⟩ := neg_occ_unique hφ v hv
    have e1 := huniq' o' ho'
    have e2 := huniq' ⟨j', i⟩ hl
    rw [e1, ← e2] at hmem
    exact hnotvar hmem
