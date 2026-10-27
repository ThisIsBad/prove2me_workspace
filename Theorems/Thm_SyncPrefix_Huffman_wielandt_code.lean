import Mathlib
import Definitions.Def_SyncPrefix_Huffman_Constructions

namespace SyncPrefix.Huffman

open Computability

/-- The Wielandt code (p. 8): for `L ≥ 1`, `Z_L = 0{0,1}^{L-1} ∪ 1{0,1}^{L}` is a maximal prefix
code with `3 · 2^{L-1}` words, of lengths `L` and `L + 1`, and the shortest word `w` with
`u w ∈ Z_L∗` for every word `u` has length between `L² − L + 1` and `L²`. -/
theorem wielandt_code (L : ℕ) (hL : 1 ≤ L) :
    IsMaximalPrefixCode (lang (wielandtCode L)) ∧
      (wielandtCode L).card = 3 * 2 ^ (L - 1) ∧
      IsLeast ((fun z : List Bool => z.length) '' (wielandtCode L : Set (List Bool))) L ∧
      IsGreatest ((fun z : List Bool => z.length) '' (wielandtCode L : Set (List Bool))) (L + 1) ∧
      (∃ w : List Bool, w.length ≤ L ^ 2 ∧ ∀ u : List Bool, u ++ w ∈ (lang (wielandtCode L))∗) ∧
      ∀ w : List Bool, (∀ u : List Bool, u ++ w ∈ (lang (wielandtCode L))∗) →
        L ^ 2 - L + 1 ≤ w.length := by sorry

end SyncPrefix.Huffman

