import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P15

noncomputable section

open scoped BigOperators Matrix

namespace QAlgorithms.Papers.Independent.Renew46.P15

attribute [local instance] Classical.propDecidable

/-- Appendix C.2, (C7)-(C9), PDF pp.17-18: predecessor validity, immediate
precedence, inclusive one-based enumeration and the extreme patterns. Q is one
plus the number of successful predecessor steps, correcting the omitted initial
pattern in the prose according to (C7), Table V and the endpoint sentence. -/
theorem gtPattern_predecessor_index {n : ℕ} (s : GTTopRow n) :
    0 < Fintype.card (Pattern s) ∧
    Function.Injective (patternRank (s := s)) ∧
    (∀ q : ℕ, (∃ m : Pattern s, patternRank m = q) ↔
      1 ≤ q ∧ q ≤ Fintype.card (Pattern s)) ∧
    (∀ a b : Pattern s, patternLt a b ↔ patternRank a < patternRank b) ∧
    (∀ m : Pattern s,
      (patternRank m = 1 ↔ ∀ (l k : Fin (n + 2)) (hkl : k ≤ l),
        patternGrid m l k = s.val ⟨k.val + (n + 1 - l.val), by
          have hl := l.isLt
          have hklNat : k.val ≤ l.val := hkl
          omega⟩) ∧
      (patternRank m = Fintype.card (Pattern s) ↔
        ∀ l k : Fin (n + 2), k ≤ l → patternGrid m l k = s.val k) ∧
      (match patternPredecessor m with
        | none => patternRank m = 1
        | some raw => ∃ p : Pattern s, patternGrid p = raw ∧
            patternRank m = patternRank p + 1 ∧
            ∀ q : Pattern s, patternLt q m → q = p ∨ patternLt q p) ∧
      HasPredecessorChain (patternRank m - 1) m ∧
      ∀ steps, HasPredecessorChain steps m → steps + 1 = patternRank m) := by sorry

end QAlgorithms.Papers.Independent.Renew46.P15

end

