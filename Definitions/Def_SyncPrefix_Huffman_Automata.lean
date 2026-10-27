import Mathlib

namespace SyncPrefix.Huffman

/-! Complete deterministic automata, synchronizing words, strongly acyclic automata and Huffman
decoders (Ryzhikov–Szykuła, arXiv:1806.06299v1, §2, pp. 2–3). An automaton is given by its
transition function `δ : σ → α → σ` (states `σ`, letters `α`); there is no initial or final state. -/

section Generic

variable {σ α : Type}

/-- The extended transition function: `run δ q w = δ(q, w)`, with `δ(q, wx) = δ(δ(q, w), x)`. -/
def run (δ : σ → α → σ) (q : σ) (w : List α) : σ := w.foldl δ q

/-- `w` is a synchronizing word: it maps every state to one and the same state `q`. -/
def IsSyncWord (δ : σ → α → σ) (w : List α) : Prop := ∃ q, ∀ q', run δ q' w = q

/-- The automaton is synchronizing: it has a synchronizing word. -/
def IsSynchronizing (δ : σ → α → σ) : Prop := ∃ w, IsSyncWord δ w

/-- The length of a shortest synchronizing word. Junk value `0` when `δ` is not synchronizing
(`sInf ∅ = 0`); every statement assumes or proves `IsSynchronizing δ`. -/
noncomputable def syncLength (δ : σ → α → σ) : ℕ :=
  sInf {ℓ | ∃ w : List α, w.length = ℓ ∧ IsSyncWord δ w}

/-- A sink state: every letter maps it to itself. -/
def IsSink (δ : σ → α → σ) (q : σ) : Prop := ∀ a, δ q a = q

/-- Strongly acyclic (p. 3): every cycle is a self-loop (a run that returns to `q` never leaves
`q`), and every state with a self-loop is a sink state. -/
def StronglyAcyclic (δ : σ → α → σ) : Prop :=
  (∀ q w, run δ q w = q → ∀ i ≤ w.length, run δ q (w.take i) = q) ∧
    (∀ q a, δ q a = q → IsSink δ q)

/-- Strongly connected: every ordered pair of states is joined by a word. -/
def StronglyConnected (δ : σ → α → σ) : Prop := ∀ q q', ∃ w, run δ q w = q'

/-- `w` is a first-return word of `r`: nonempty, maps `r` to `r`, and no nonempty proper prefix
maps `r` to `r`. -/
def IsFirstReturn (δ : σ → α → σ) (r : σ) (w : List α) : Prop :=
  w ≠ [] ∧ run δ r w = r ∧ ∀ i, 0 < i → i < w.length → run δ r (w.take i) ≠ r

/-- A Huffman decoder (p. 3): a strongly connected complete automaton with a state `r` whose set
of first-return words is finite (that set is then a finite maximal prefix code). -/
def IsHuffmanDecoder (δ : σ → α → σ) : Prop :=
  StronglyConnected δ ∧ ∃ r, {w | IsFirstReturn δ r w}.Finite

end Generic

/-- An instance of Short Sync Word restricted to complete automata: `n` states `Fin n`,
`k` letters `Fin k`, and the transition table `δ`. -/
structure Automaton where
  n : ℕ
  k : ℕ
  δ : Fin n → Fin k → Fin n

/-- Encoding over `Option Bool`: `n` in unary (`some true`), a separator `none`, `k` in unary,
`none`, then for each state `q` and each letter `a` (in increasing order) the value `δ q a` in
unary followed by `none`. -/
def Automaton.encode (A : Automaton) : List (Option Bool) :=
  List.replicate A.n (some true) ++ none :: List.replicate A.k (some true) ++ none ::
    (List.finRange A.n).flatMap fun q =>
      (List.finRange A.k).flatMap fun a => List.replicate (A.δ q a).val (some true) ++ [none]

end SyncPrefix.Huffman
