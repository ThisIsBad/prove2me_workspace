import Mathlib
import Definitions.Def_SyncPrefix_Huffman_Constructions

namespace SyncPrefix.Huffman

open Computability

/-- The composition bounds of the proof of Corollary 8 (p. 8), in decoder form. Let `δY` be a
synchronizing complete automaton over `β`, `Z` a finite maximal prefix code over `α` with
shortest and longest codeword lengths `m` and `M`, `e : β → Z` a bijection, and `w_Z` a word
with `u w_Z ∈ Z∗` for every word `u`. Then the composition decoder is synchronizing and
`m ℓ ≤ ℓ_X ≤ M ℓ + |w_Z|`, where `ℓ` and `ℓ_X` are the lengths of shortest synchronizing words of
`δY` and of the decoder. -/
theorem composition_bounds {σ α β : Type} [DecidableEq α] (δY : σ → β → σ)
    (Z : Finset (List α)) (hZ : IsMaximalPrefixCode (lang Z)) (e : β ≃ {z // z ∈ Z})
    (m M : ℕ) (hm : IsLeast ((fun z : List α => z.length) '' (Z : Set (List α))) m)
    (hM : IsGreatest ((fun z : List α => z.length) '' (Z : Set (List α))) M)
    (wZ : List α) (hwZ : ∀ u : List α, u ++ wZ ∈ (lang Z)∗) (hY : IsSynchronizing δY) :
    IsSynchronizing (composeDecoder δY Z e) ∧
      m * syncLength δY ≤ syncLength (composeDecoder δY Z e) ∧
      syncLength (composeDecoder δY Z e) ≤ M * syncLength δY + wZ.length := by sorry

end SyncPrefix.Huffman

