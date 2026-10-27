import Mathlib
import Definitions.Def_EdgeDomSets_NPC_Construction

open EdgeDomSets.NPC

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

theorem var_mem_variablesList {φ : CookLevin.Formula} (o : Occ φ) :
    (occLit o).var ∈ CookLevin.variablesList φ := by
  rw [CookLevin.mem_variablesList_iff]
  exact ⟨φ.get o.1, List.get_mem _ _, occLit o, List.get_mem _ _, rfl⟩

theorem card_negate_le {φ : CookLevin.Formula} (hφ : IsSat3Restricted φ) (o : Occ φ) :
    (Finset.univ.filter fun o' : Occ φ => occLit o' = (occLit o).negate).card ≤ 2 := by
  rw [card_occ_filter]
  have h := hφ.2 _ (var_mem_variablesList o)
  cases hl : occLit o with
  | Pos v =>
    rw [hl] at h
    simp only [CookLevin.Literal.var] at h
    have : negCount φ v = (φ.map fun c => c.count (CookLevin.Literal.Neg v)).sum := rfl
    simp only [CookLevin.Literal.negate]
    omega
  | Neg v =>
    rw [hl] at h
    simp only [CookLevin.Literal.var] at h
    have : posCount φ v = (φ.map fun c => c.count (CookLevin.Literal.Pos v)).sum := rfl
    simp only [CookLevin.Literal.negate]
    omega

/-- positions in clause `j` whose literal has sign `b` -/
def litIdx (φ : CookLevin.Formula) (j : Fin φ.length) (b : Bool) :
    Finset (Fin (φ.get j).length) :=
  Finset.univ.filter fun i => isPos ((φ.get j).get i) = b

/-- the neighbourhood of a vertex of `G` -/
def nbr (φ : CookLevin.Formula) : GV φ → Finset (GV φ)
  | Sum.inl (Sum.inl o) => {pend o, varNode o, clauseNode o}
  | Sum.inl (Sum.inr (Sum.inl o)) => {lit o}
  | Sum.inl (Sum.inr (Sum.inr o)) =>
      {lit o} ∪ (Finset.univ.filter fun o' : Occ φ => occLit o' = (occLit o).negate).image varNode
  | Sum.inr (Sum.inl j) => {dNode' j} ∪ (litIdx φ j true).image fun i => lit ⟨j, i⟩
  | Sum.inr (Sum.inr j) => {dNode j} ∪ (litIdx φ j false).image fun i => lit ⟨j, i⟩

theorem clauseNode_eq {φ : CookLevin.Formula} (o : Occ φ) :
    clauseNode o = if isPos (occLit o) = true then dNode o.1 else dNode' o.1 := by
  unfold clauseNode; split_ifs <;> simp_all

theorem GRel_mem_nbr {φ : CookLevin.Formula} {a b : GV φ} (h : GRel φ a b) :
    b ∈ nbr φ a ∧ a ∈ nbr φ b := by
  rcases h with ⟨o, rfl, rfl⟩ | ⟨o, rfl, rfl⟩ | ⟨o, rfl, rfl⟩ | ⟨j, rfl, rfl⟩ |
      ⟨o, o', v, ho, ho', rfl, rfl⟩
  · simp [nbr, lit, pend]
  · simp [nbr, lit, varNode]
  · refine ⟨by simp [nbr, lit], ?_⟩
    rw [clauseNode_eq]
    obtain ⟨j, i⟩ := o
    split_ifs with h
    · simp only [nbr, dNode, Finset.mem_union, Finset.mem_image, litIdx, Finset.mem_filter,
        Finset.mem_univ, true_and]
      exact Or.inr ⟨i, h, rfl⟩
    · simp only [nbr, dNode', Finset.mem_union, Finset.mem_image, litIdx, Finset.mem_filter,
        Finset.mem_univ, true_and]
      exact Or.inr ⟨i, by rw [Bool.eq_false_iff]; exact h, rfl⟩
  · simp [nbr, dNode, dNode']
  · simp only [nbr, varNode, Finset.mem_union, Finset.mem_image, Finset.mem_filter,
      Finset.mem_univ, true_and, ho, ho', CookLevin.Literal.negate]
    exact ⟨Or.inr ⟨o', ho', rfl⟩, Or.inr ⟨o, ho, rfl⟩⟩

theorem adj_mem_nbr {φ : CookLevin.Formula} {a b : GV φ} (h : (G φ).Adj a b) : b ∈ nbr φ a := by
  rw [G, SimpleGraph.fromRel_adj] at h
  rcases h.2 with h | h
  · exact (GRel_mem_nbr h).1
  · exact (GRel_mem_nbr h).2

theorem degreeLE_of_card {φ : CookLevin.Formula} (w : GV φ) (m : ℕ) (h : (nbr φ w).card ≤ m) :
    DegreeLE (G φ) w m := by
  intro s hs
  exact le_trans (Finset.card_le_card fun v hv => adj_mem_nbr (hs v hv)) h

theorem card_le_of_not_degreeLE {φ : CookLevin.Formula} (w : GV φ) (m : ℕ)
    (h : ¬ DegreeLE (G φ) w m) : m + 1 ≤ (nbr φ w).card := by
  unfold DegreeLE at h
  push Not at h
  obtain ⟨s, hs, hcard⟩ := h
  exact le_trans hcard (Finset.card_le_card fun v hv => adj_mem_nbr (hs v hv))

theorem not_degreeLE_of_card {φ : CookLevin.Formula} (w : GV φ) (m : ℕ)
    (hadj : ∀ v ∈ nbr φ w, (G φ).Adj w v) (h : m + 1 ≤ (nbr φ w).card) :
    ¬ DegreeLE (G φ) w m := by
  intro hd
  have := hd (nbr φ w) hadj
  omega

theorem card_litIdx_le {φ : CookLevin.Formula} (j : Fin φ.length) (b : Bool) :
    (litIdx φ j b).card ≤ (φ.get j).length := by
  unfold litIdx
  exact le_trans (Finset.card_filter_le _ _) (by simp)

theorem card_nbr_d {φ : CookLevin.Formula} (j : Fin φ.length) :
    (nbr φ (dNode j)).card = 1 + (litIdx φ j true).card := by
  simp only [nbr, dNode]
  rw [Finset.card_union_of_disjoint, Finset.card_singleton, Finset.card_image_of_injective]
  · intro i i' h
    simpa [lit] using h
  · rw [Finset.disjoint_left]
    intro v hv hv'
    rw [Finset.mem_singleton] at hv
    subst hv
    obtain ⟨i, -, hi⟩ := Finset.mem_image.mp hv'
    simp [lit, dNode'] at hi

theorem card_nbr_d' {φ : CookLevin.Formula} (j : Fin φ.length) :
    (nbr φ (dNode' j)).card = 1 + (litIdx φ j false).card := by
  simp only [nbr, dNode']
  rw [Finset.card_union_of_disjoint, Finset.card_singleton, Finset.card_image_of_injective]
  · intro i i' h
    simpa [lit] using h
  · rw [Finset.disjoint_left]
    intro v hv hv'
    rw [Finset.mem_singleton] at hv
    subst hv
    obtain ⟨i, -, hi⟩ := Finset.mem_image.mp hv'
    simp [lit, dNode] at hi

theorem card_nbr_le {φ : CookLevin.Formula} (hφ : IsSat3Restricted φ) (w : GV φ) :
    (nbr φ w).card ≤ 4 := by
  have hlen : ∀ j : Fin φ.length, (φ.get j).length ≤ 3 := fun j => hφ.1 _ (List.get_mem _ _)
  rcases w with ((o | o | o) | (j | j))
  · show ({pend o, varNode o, clauseNode o} : Finset (GV φ)).card ≤ 4
    exact le_trans (Finset.card_le_three (a := pend o) (b := varNode o) (c := clauseNode o)) (by norm_num)
  · simp [nbr]
  · simp only [nbr]
    refine le_trans (Finset.card_union_le _ _) ?_
    rw [Finset.card_singleton]
    have := le_trans (Finset.card_image_le (f := varNode)
      (s := Finset.univ.filter fun o' : Occ φ => occLit o' = (occLit o).negate))
      (card_negate_le hφ o)
    omega
  · show (nbr φ (dNode j)).card ≤ 4
    rw [card_nbr_d]
    have := card_litIdx_le j true
    have := hlen j
    omega
  · show (nbr φ (dNode' j)).card ≤ 4
    rw [card_nbr_d']
    have := card_litIdx_le j false
    have := hlen j
    omega

theorem card_nbr_le_three {φ : CookLevin.Formula} (hφ : IsSat3Restricted φ)
    (o : Occ φ) :
    (nbr φ (lit o)).card ≤ 3 ∧ (nbr φ (pend o)).card ≤ 3 ∧ (nbr φ (varNode o)).card ≤ 3 := by
  refine ⟨?_, by simp [nbr, pend], ?_⟩
  · show ({pend o, varNode o, clauseNode o} : Finset (GV φ)).card ≤ 3
    exact Finset.card_le_three (a := pend o) (b := varNode o) (c := clauseNode o)
  simp only [nbr, varNode]
  refine le_trans (Finset.card_union_le _ _) ?_
  rw [Finset.card_singleton]
  have := le_trans (Finset.card_image_le (f := varNode)
    (s := Finset.univ.filter fun o' : Occ φ => occLit o' = (occLit o).negate))
    (card_negate_le hφ o)
  omega

theorem nbr_d_adj {φ : CookLevin.Formula} (j : Fin φ.length) :
    ∀ v ∈ nbr φ (dNode j), (G φ).Adj (dNode j) v := by
  intro v hv
  simp only [nbr, dNode, Finset.mem_union, Finset.mem_singleton, Finset.mem_image, litIdx,
    Finset.mem_filter, Finset.mem_univ, true_and] at hv
  rcases hv with rfl | ⟨i, hi, rfl⟩
  · rw [G, SimpleGraph.fromRel_adj]
    exact ⟨by simp [dNode, dNode'], Or.inl (Or.inr (Or.inr (Or.inr (Or.inl ⟨j, rfl, rfl⟩))))⟩
  · apply SimpleGraph.Adj.symm
    rw [G, SimpleGraph.fromRel_adj]
    refine ⟨by simp [dNode, lit], Or.inl (Or.inr (Or.inr (Or.inl ⟨⟨j, i⟩, rfl, ?_⟩)))⟩
    have hi' : isPos (occLit ⟨j, i⟩) = true := hi
    rw [clauseNode_eq, if_pos hi']

theorem nbr_d'_adj {φ : CookLevin.Formula} (j : Fin φ.length) :
    ∀ v ∈ nbr φ (dNode' j), (G φ).Adj (dNode' j) v := by
  intro v hv
  simp only [nbr, dNode', Finset.mem_union, Finset.mem_singleton, Finset.mem_image, litIdx,
    Finset.mem_filter, Finset.mem_univ, true_and] at hv
  rcases hv with rfl | ⟨i, hi, rfl⟩
  · apply SimpleGraph.Adj.symm
    rw [G, SimpleGraph.fromRel_adj]
    exact ⟨by simp [dNode, dNode'], Or.inl (Or.inr (Or.inr (Or.inr (Or.inl ⟨j, rfl, rfl⟩))))⟩
  · apply SimpleGraph.Adj.symm
    rw [G, SimpleGraph.fromRel_adj]
    refine ⟨by simp [dNode', lit], Or.inl (Or.inr (Or.inr (Or.inl ⟨⟨j, i⟩, rfl, ?_⟩)))⟩
    have hi' : isPos (occLit ⟨j, i⟩) = false := hi
    rw [clauseNode_eq, if_neg (by simp [hi'])]

theorem isPos_eq_iff (l : CookLevin.Literal) (b : Bool) :
    isPos l = b ↔ (if b then ∃ v, l = .Pos v else ∃ v, l = .Neg v) := by
  cases l <;> cases b <;> simp [isPos]

theorem litIdx_card_iff {φ : CookLevin.Formula} (j : Fin φ.length) (b : Bool) :
    (φ.get j).length ≤ (litIdx φ j b).card ↔ ∀ l ∈ φ.get j, isPos l = b := by
  constructor
  · intro h
    have h' : (litIdx φ j b).card = Fintype.card (Fin (φ.get j).length) := by
      rw [Fintype.card_fin]
      exact le_antisymm (card_litIdx_le j b) h
    have hu := Finset.eq_univ_of_card _ h'
    intro l hl
    obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hl
    have hi : i ∈ litIdx φ j b := hu ▸ Finset.mem_univ i
    simpa [litIdx] using hi
  · intro h
    have : litIdx φ j b = Finset.univ := by
      ext i
      simp only [litIdx, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
      exact h _ (List.get_mem _ _)
    rw [this, Finset.card_univ, Fintype.card_fin]

theorem d_iff {φ : CookLevin.Formula} (hφ : IsSat3Restricted φ) (j : Fin φ.length) :
    ¬ DegreeLE (G φ) (dNode j) 3 ↔
      (φ.get j).length = 3 ∧ ∀ l ∈ φ.get j, ∃ v, l = CookLevin.Literal.Pos v := by
  have hlen : (φ.get j).length ≤ 3 := hφ.1 _ (List.get_mem _ _)
  have hle := card_litIdx_le j true
  have key : ¬ DegreeLE (G φ) (dNode j) 3 ↔ 4 ≤ (nbr φ (dNode j)).card :=
    ⟨card_le_of_not_degreeLE _ _, not_degreeLE_of_card _ _ (nbr_d_adj j)⟩
  rw [key, card_nbr_d]
  constructor
  · intro h
    have h1 : (φ.get j).length = 3 := by omega
    refine ⟨h1, ?_⟩
    have := (litIdx_card_iff j true).mp (by omega)
    intro l hl
    exact ((isPos_eq_iff l true).mp (this l hl))
  · rintro ⟨h1, h2⟩
    have := (litIdx_card_iff j true).mpr (fun l hl => (isPos_eq_iff l true).mpr (by simpa using h2 l hl))
    omega

theorem d'_iff {φ : CookLevin.Formula} (hφ : IsSat3Restricted φ) (j : Fin φ.length) :
    ¬ DegreeLE (G φ) (dNode' j) 3 ↔
      (φ.get j).length = 3 ∧ ∀ l ∈ φ.get j, ∃ v, l = CookLevin.Literal.Neg v := by
  have hlen : (φ.get j).length ≤ 3 := hφ.1 _ (List.get_mem _ _)
  have hle := card_litIdx_le j false
  have key : ¬ DegreeLE (G φ) (dNode' j) 3 ↔ 4 ≤ (nbr φ (dNode' j)).card :=
    ⟨card_le_of_not_degreeLE _ _, not_degreeLE_of_card _ _ (nbr_d'_adj j)⟩
  rw [key, card_nbr_d']
  constructor
  · intro h
    have h1 : (φ.get j).length = 3 := by omega
    refine ⟨h1, ?_⟩
    have := (litIdx_card_iff j false).mp (by omega)
    intro l hl
    exact ((isPos_eq_iff l false).mp (this l hl))
  · rintro ⟨h1, h2⟩
    have := (litIdx_card_iff j false).mpr (fun l hl => (isPos_eq_iff l false).mpr (by simpa using h2 l hl))
    omega

theorem solution (φ : CookLevin.Formula) (hφ : IsSat3Restricted φ) :
    MaxDegreeLE (G φ) 4 ∧
      ∀ w : GV φ, ¬ DegreeLE (G φ) w 3 ↔
        ∃ j : Fin φ.length, (φ.get j).length = 3 ∧
          ((w = dNode j ∧ ∀ l ∈ φ.get j, ∃ v, l = CookLevin.Literal.Pos v) ∨
            (w = dNode' j ∧ ∀ l ∈ φ.get j, ∃ v, l = CookLevin.Literal.Neg v)) := by
  refine ⟨fun w => degreeLE_of_card w 4 (card_nbr_le hφ w), ?_⟩
  intro w
  rcases w with ((o | o | o) | (j | j))
  · constructor
    · intro h
      have := card_le_of_not_degreeLE _ _ h
      have := (card_nbr_le_three hφ o).1
      simp [lit] at *
      omega
    · rintro ⟨j, -, ⟨h, -⟩ | ⟨h, -⟩⟩ <;> simp [dNode, dNode'] at h
  · constructor
    · intro h
      have := card_le_of_not_degreeLE _ _ h
      have := (card_nbr_le_three hφ o).2.1
      simp [pend] at *
      omega
    · rintro ⟨j, -, ⟨h, -⟩ | ⟨h, -⟩⟩ <;> simp [dNode, dNode'] at h
  · constructor
    · intro h
      have := card_le_of_not_degreeLE _ _ h
      have := (card_nbr_le_three hφ o).2.2
      simp [varNode] at *
      omega
    · rintro ⟨j, -, ⟨h, -⟩ | ⟨h, -⟩⟩ <;> simp [dNode, dNode'] at h
  · rw [show (Sum.inr (Sum.inl j) : GV φ) = dNode j from rfl, d_iff hφ j]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨j, h1, Or.inl ⟨rfl, h2⟩⟩
    · rintro ⟨j', h1, ⟨h, h2⟩ | ⟨h, -⟩⟩
      · have : j = j' := by simpa [dNode] using h
        subst this
        exact ⟨h1, h2⟩
      · simp [dNode, dNode'] at h
  · rw [show (Sum.inr (Sum.inr j) : GV φ) = dNode' j from rfl, d'_iff hφ j]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨j, h1, Or.inr ⟨rfl, h2⟩⟩
    · rintro ⟨j', h1, ⟨h, -⟩ | ⟨h, h2⟩⟩
      · simp [dNode, dNode'] at h
      · have : j = j' := by simpa [dNode'] using h
        subst this
        exact ⟨h1, h2⟩
