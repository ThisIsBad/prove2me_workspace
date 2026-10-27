import Mathlib
import Definitions.Def_SyncPrefix_Huffman_Constructions

namespace SyncPrefix.Huffman

/-- Theorem 7 (p. 7): the composition `X = Y ∘ Z` of two synchronizing complete codes, `Z`
finite with shortest and longest codeword lengths `m` and `M`, is synchronizing, and its
shortest absorbing pair has length between `m ℓ` and `2 M ℓ + 2 c`, where `ℓ` and `c` are the
lengths of shortest absorbing pairs of `Y` and `Z`. -/
theorem theorem_7 {α β : Type} (Y : Language β) (Z : Language α)
    (hY : IsSyncCode Y) (hZ : IsSyncCode Z) (hZfin : Set.Finite (Z : Set (List α)))
    (e : β ≃ {z // z ∈ Z}) (m M : ℕ)
    (hm : IsLeast ((fun z : List α => z.length) '' (Z : Set (List α))) m)
    (hM : IsGreatest ((fun z : List α => z.length) '' (Z : Set (List α))) M) :
    IsSyncCode (compose Y Z e) ∧ m * absorbLength Y ≤ absorbLength (compose Y Z e) ∧
      absorbLength (compose Y Z e) ≤ 2 * M * absorbLength Y + 2 * absorbLength Z := by sorry

end SyncPrefix.Huffman

