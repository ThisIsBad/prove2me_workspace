import Mathlib
import Definitions.Def_ProjSchedTW_Complexity_Encoding

namespace SchedComplexity.NoWait

open ProjSchedTW.Complexity (BSym encNats)

/-- A Hamilton path of the directed graph on the vertex set `Fin n` with arc relation `adj`
(`adj u v = true` iff `(u, v)` is an arc): an ordering `σ 0, σ 1, …, σ (n-1)` of all vertices,
each vertex exactly once (`σ` is a bijection of `Fin n`), such that every two consecutive
vertices are joined by an arc `(σ i, σ (i+1))` (Theorem 2(d), p. 14: "a directed path passing
through each vertex exactly once"). Loops `adj v v` play no role. For `n = 0` and `n = 1` every
graph has a Hamilton path (the empty path, the one-vertex path). -/
def HasHamiltonPath {n : ℕ} (adj : Fin n → Fin n → Bool) : Prop :=
  ∃ σ : Fin n ≃ Fin n, ∀ (i : Fin n) (h : i.val + 1 < n), adj (σ i) (σ ⟨i.val + 1, h⟩) = true

/-- A Hamilton circuit of the directed graph on `Fin n` with arc relation `adj`: a cyclic
ordering `σ 0, …, σ (n-1)` of all vertices with arcs `(σ i, σ (i+1))` for `i < n-1` and the
closing arc `(σ (n-1), σ 0)` (Theorem 2(c), p. 14: "a directed cycle passing through each vertex
exactly once"). `finRotate n` sends `i` to `i + 1 mod n`. For `n = 1` the closing arc is a loop
`(v, v)`, so a one-vertex graph has a Hamilton circuit iff it has a loop; for `n = 0` the
condition is vacuous. -/
def HasHamiltonCircuit {n : ℕ} (adj : Fin n → Fin n → Bool) : Prop :=
  ∃ σ : Fin n ≃ Fin n, ∀ i : Fin n, adj (σ i) (σ (finRotate n i)) = true

/-- The code of a directed graph on `Fin n`: the list of natural numbers `n`, followed by the
adjacency matrix row by row (entry `1` for an arc, `0` otherwise, diagonal included), written
in binary with `encNats`. The code determines `n` and `adj`. -/
def dhpCode {n : ℕ} (adj : Fin n → Fin n → Bool) : List BSym :=
  encNats (n :: (List.ofFn fun u : Fin n => List.ofFn fun v : Fin n =>
    if adj u v then 1 else 0).flatten)

/-- DIRECTED HAMILTON PATH (Theorem 2(d), p. 14) as a language: the codes `dhpCode adj` of the
directed graphs that have a Hamilton path. -/
def dhpLang : CookPvsNP.Lang BSym :=
  { w | ∃ (n : ℕ) (adj : Fin n → Fin n → Bool), HasHamiltonPath adj ∧ w = dhpCode adj }

end SchedComplexity.NoWait
