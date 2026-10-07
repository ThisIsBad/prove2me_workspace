import Mathlib
import Definitions.Def_FibHeap_Amort_Model

namespace FibHeap.Amort
theorem potential_makeHeap_findMin_insert_meld (s s' : Coll) (op : Op) (d : StepData)
    (hstep : Step s op s' d) :
    ((op = .makeHeap ∨ (∃ h, op = .findMin h) ∨ (∃ h₁ h₂, op = .meld h₁ h₂)) →
        potential s' = potential s) ∧
      (∀ (i : ℕ) (k : ℝ) (h : ℕ), op = .insert i k h →
        potential s' = potential s + 1) := by sorry
end FibHeap.Amort

