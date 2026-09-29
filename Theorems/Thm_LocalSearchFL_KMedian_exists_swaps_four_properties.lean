import Mathlib
import Definitions.Def_LocalSearchFL_KMedian_captures

namespace LocalSearchFL.KMedian

/-- The k swaps of §3.2 (pp. 549–550): when `|S| = |O|`, one can assign to each `o ∈ O` a
facility `η o ∈ S` (the swap `⟨η o, o⟩`) such that
(1) each `o ∈ O` is in exactly one swap (built into `η` being a function on `O`);
(2) a facility of `S` capturing more than one facility of `O` is in no swap;
(3) each good facility of `S` is in at most two swaps;
(4) if `⟨s, o⟩` is a swap, then `s` captures no facility `o' ∈ O` with `o' ≠ o`. -/
theorem exists_swaps_four_properties {Cl Fa : Type} [Fintype Cl] [DecidableEq Cl]
    [DecidableEq Fa]
    (σS σO : Cl → Fa) (S O : Finset Fa) (hcard : S.card = O.card) :
    ∃ η : Fa → Fa,
      (∀ o ∈ O, η o ∈ S) ∧
      (∀ s ∈ S, (∃ o₁ ∈ O, ∃ o₂ ∈ O, o₁ ≠ o₂ ∧ captures σS σO s o₁ ∧ captures σS σO s o₂) →
        ∀ o ∈ O, η o ≠ s) ∧
      (∀ s ∈ S, IsGood σS σO O s → (O.filter (fun o => η o = s)).card ≤ 2) ∧
      (∀ o ∈ O, ∀ o' ∈ O, o' ≠ o → ¬ captures σS σO (η o) o') := by sorry

end LocalSearchFL.KMedian

