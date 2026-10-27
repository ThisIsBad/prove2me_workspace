import Mathlib
import Definitions.Def_EdgeDomSets_NPC_Construction

open EdgeDomSets.NPC

set_option maxRecDepth 100000

instance HAdjDec : DecidableRel H.Adj := fun a b =>
  inferInstanceAs (Decidable (a ≠ b ∧ ((a, b) ∈ HEdges ∨ (b, a) ∈ HEdges)))

/-- weighted double counting -/
theorem weight_bound (L : Finset (Fin 14 × Fin 14)) (w : Fin 14 × Fin 14 → ℕ) (M : ℕ)
    (D : Finset (Sym2 (Fin 14)))
    (hcov : ∀ p ∈ L, ∃ f ∈ D, p.1 ∈ f ∨ p.2 ∈ f)
    (hbound : ∀ f ∈ D, (L.filter fun p => p.1 ∈ f ∨ p.2 ∈ f).sum w ≤ M) :
    L.sum w ≤ M * D.card := by
  calc L.sum w ≤ ∑ p ∈ L, ∑ f ∈ D, (if p.1 ∈ f ∨ p.2 ∈ f then w p else 0) := by
        apply Finset.sum_le_sum
        intro p hp
        obtain ⟨f, hf, hpf⟩ := hcov p hp
        calc w p = (if p.1 ∈ f ∨ p.2 ∈ f then w p else 0) := by rw [if_pos hpf]
          _ ≤ _ := Finset.single_le_sum (f := fun f => if p.1 ∈ f ∨ p.2 ∈ f then w p else 0)
              (fun _ _ => by positivity) hf
    _ = ∑ f ∈ D, ∑ p ∈ L, (if p.1 ∈ f ∨ p.2 ∈ f then w p else 0) := Finset.sum_comm
    _ = ∑ f ∈ D, (L.filter fun p => p.1 ∈ f ∨ p.2 ∈ f).sum w := by
        apply Finset.sum_congr rfl
        intro f _
        rw [Finset.sum_filter]
    _ ≤ ∑ f ∈ D, M := Finset.sum_le_sum hbound
    _ = M * D.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]

/-- the weight of a pair: `1` for the edges at `u` and `v`, `2` otherwise -/
def wt (p : Fin 14 × Fin 14) : ℕ :=
  if p.1 = hu ∨ p.2 = hu ∨ p.1 = hv ∨ p.2 = hv then 1 else 2

/-- the twelve edges of `H` not incident with a corner -/
def innerE : Finset (Fin 14 × Fin 14) :=
  {(ha1, ha2), (ha2, ha3), (hb1, hb2), (hb2, hb3), (hc1, hc2), (hc2, hc3),
   (hu, ha1), (hu, hb3), (hu, hc1), (hv, hb1), (hv, ha3), (hv, hc3)}

/-- all eighteen edges of `H` -/
def allE : Finset (Fin 14 × Fin 14) :=
  {(hx, ha1), (ha1, ha2), (ha2, ha3), (ha3, hy),
   (hx, hb1), (hb1, hb2), (hb2, hb3), (hb3, hz),
   (hy, hc1), (hc1, hc2), (hc2, hc3), (hc3, hz),
   (hu, ha1), (hu, hb3), (hu, hc1), (hv, hb1), (hv, ha3), (hv, hc3)}

theorem cov_of_eds (S : Finset (Fin 3)) (D : Finset (Sym2 (Fin 14))) (hD : EdsRestricted S D)
    (L : Finset (Fin 14 × Fin 14)) (hL : ∀ p ∈ L, H.Adj p.1 p.2)
    (hcorner : ∀ p ∈ L, ∀ s ∈ S, attach s ∉ s(p.1, p.2)) :
    ∀ p ∈ L, ∃ f ∈ D, p.1 ∈ f ∨ p.2 ∈ f := by
  intro p hp
  by_cases hmem : s(p.1, p.2) ∈ D
  · exact ⟨_, hmem, Or.inl (Sym2.mem_mk_left _ _)⟩
  · rcases hD.2 _ (hL p hp) hmem with ⟨f, hf, w, hw, hwf⟩ | ⟨s, hs, hsp⟩
    · refine ⟨f, hf, ?_⟩
      rw [Sym2.mem_iff] at hw
      rcases hw with rfl | rfl
      · exact Or.inl hwf
      · exact Or.inr hwf
    · exact absurd hsp (hcorner p hp s hs)

theorem bound_of_eds (S : Finset (Fin 3)) (D : Finset (Sym2 (Fin 14))) (hD : EdsRestricted S D)
    (L : Finset (Fin 14 × Fin 14)) (M : ℕ)
    (hb : ∀ a b : Fin 14, H.Adj a b → (L.filter fun p => p.1 ∈ s(a, b) ∨ p.2 ∈ s(a, b)).sum wt ≤ M) :
    ∀ f ∈ D, (L.filter fun p => p.1 ∈ f ∨ p.2 ∈ f).sum wt ≤ M := by
  intro f hf
  have := hD.1 f hf
  induction f using Sym2.ind with
  | h a b =>
    rw [SimpleGraph.mem_edgeSet] at this
    exact hb a b this

theorem innerE_adj : ∀ p ∈ innerE, H.Adj p.1 p.2 := by decide
theorem innerE_corner : ∀ p ∈ innerE, ∀ s : Fin 3, attach s ∉ s(p.1, p.2) := by decide
theorem innerE_bound : ∀ a b : Fin 14, H.Adj a b →
    (innerE.filter fun p => p.1 ∈ s(a, b) ∨ p.2 ∈ s(a, b)).sum wt ≤ 5 := by decide
theorem innerE_sum : innerE.sum wt = 18 := by decide
theorem allE_adj : ∀ p ∈ allE, H.Adj p.1 p.2 := by decide
theorem allE_bound : ∀ a b : Fin 14, H.Adj a b →
    (allE.filter fun p => p.1 ∈ s(a, b) ∨ p.2 ∈ s(a, b)).sum wt ≤ 7 := by decide
theorem allE_sum : allE.sum wt = 30 := by decide

theorem four_needed (S : Finset (Fin 3)) (D : Finset (Sym2 (Fin 14))) (hD : EdsRestricted S D) :
    4 ≤ D.card := by
  have h := weight_bound innerE wt 5 D
    (cov_of_eds S D hD innerE innerE_adj (fun p hp s _ => innerE_corner p hp s))
    (bound_of_eds S D hD innerE 5 innerE_bound)
  have h18 := innerE_sum
  omega

theorem five_needed (D : Finset (Sym2 (Fin 14))) (hD : EdsRestricted ∅ D) : 5 ≤ D.card := by
  have h := weight_bound allE wt 7 D
    (cov_of_eds ∅ D hD allE allE_adj (fun p _ s hs => by simp at hs))
    (bound_of_eds ∅ D hD allE 7 allE_bound)
  have h30 := allE_sum
  omega

def P3 : Fin 3 → Fin 5 → Fin 14 :=
  ![![hu, ha1, ha2, ha3, hv], ![hu, hb3, hb2, hb1, hv], ![hu, hc1, hc2, hc3, hv]]

theorem solution :
    (∃ P : Fin 3 → Fin 5 → Fin 14,
      (∀ i, P i 0 = hu ∧ P i 4 = hv) ∧
      (∀ i (k : Fin 4), H.Adj (P i k.castSucc) (P i k.succ)) ∧
      (∀ i k, P i k ≠ hx ∧ P i k ≠ hy ∧ P i k ≠ hz) ∧
      (∀ i i' (k k' : Fin 5), 0 < k → k < 4 → P i k = P i' k' → i = i' ∧ k = k') ∧
      (∀ w, w ≠ hx → w ≠ hy → w ≠ hz → ∃ i k, P i k = w) ∧
      (∀ a b, a ≠ hx → a ≠ hy → a ≠ hz → b ≠ hx → b ≠ hy → b ≠ hz → H.Adj a b →
        ∃ (i : Fin 3) (k : Fin 4), s(a, b) = s(P i k.castSucc, P i k.succ))) ∧
    ∀ (S : Finset (Fin 3)) (D : Finset (Sym2 (Fin 14))), EdsRestricted S D → 4 ≤ D.card := by
  refine ⟨⟨P3, by decide, by decide, by decide, by decide, by decide, by decide⟩, four_needed⟩
