import Mathlib
import Definitions.Def_SyncPrefix_Huffman_Constructions

namespace SyncPrefix.Huffman

/-- The composition decoder (pp. 7–8). Let `δY` be a complete automaton over `β` and `Z` a finite
maximal prefix code over a finite nonempty alphabet `α`, with a bijection `e : β → Z`. The decoder obtained
by hanging a copy of the tree `T_Z` from every state:
(a) has `n_Y (n_Z − 1) / |α|` states, where `n_Y` is the number of states of `δY` and `n_Z` the
number of vertices of `T_Z`;
(b) is strongly connected if `δY` is, and is a Huffman decoder if `δY` is;
(c) for every state `r`, the words returning `r` to itself in the decoder are exactly the
substitutions `β(y)` of the words `y` returning `r` to itself in `δY` (so it recognizes the star
of `X = Y ∘ Z` when `δY` recognizes `Y∗`). -/
theorem composition_decoder {σ α β : Type} [Fintype σ] [DecidableEq σ] [Fintype α] [Nonempty α]
    [DecidableEq α] (δY : σ → β → σ) (Z : Finset (List α))
    (hZ : IsMaximalPrefixCode (lang Z)) (e : β ≃ {z // z ∈ Z}) :
    Fintype.card α * Fintype.card (DecoderState σ Z) + Fintype.card σ =
        Fintype.card σ * (allPrefixes Z).card ∧
      (StronglyConnected δY → StronglyConnected (composeDecoder δY Z e)) ∧
      (IsHuffmanDecoder δY → IsHuffmanDecoder (composeDecoder δY Z e)) ∧
      ∀ (r : σ) (w : List α), run (composeDecoder δY Z e) (rootState Z r) w = rootState Z r ↔
        ∃ y : List β, run δY r y = r ∧ w = subst e y := by sorry

end SyncPrefix.Huffman

