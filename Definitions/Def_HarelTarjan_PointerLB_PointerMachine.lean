import Mathlib
import Definitions.Def_HarelTarjan_PointerLB_BinaryTree

namespace HarelTarjan.PointerLB

/-- The nodes accessible from the node `a` in `j` steps or less (proof of Theorem 1, p. 340), in a
list structure on the node type `N` in which every node has two pointer fields: `ptr m i` is the
content of field `i` of node `m`, either a node (`some b`) or nil (`none`).
`acc ptr 0 a = {a}`, and a node is accessible in `j + 1` steps or less if it is accessible in `j`
steps or less, or is the content of a pointer field of such a node. -/
def acc {N : Type*} (ptr : N → Fin 2 → Option N) : ℕ → N → Set N
  | 0, a => {a}
  | j + 1, a => acc ptr j a ∪ {b | ∃ m ∈ acc ptr j a, ∃ i : Fin 2, ptr m i = some b}

/-- A run of a pointer machine that answers a query (§2, p. 340). The machine is given pointers to
the two input nodes `a` and `b`; `Run ptr a b t held` says that after `t` steps it can hold
pointers to exactly the nodes in the list `held`. Each step dereferences one pointer field of a
node it already holds and adds the node found there. -/
inductive Run {N : Type*} (ptr : N → Fin 2 → Option N) (a b : N) : ℕ → List N → Prop
  | start : Run ptr a b 0 [a, b]
  | step {t : ℕ} {held : List N} {m n : N} (i : Fin 2) :
      Run ptr a b t held → m ∈ held → ptr m i = some n → Run ptr a b (t + 1) (n :: held)

/-- A query with input nodes `a`, `b` whose answer is the node `target` can be answered in `k`
steps: some run of at most `k` steps from `a`, `b` holds a pointer to `target`. -/
def AnsweredIn {N : Type*} (ptr : N → Fin 2 → Option N) (a b target : N) (k : ℕ) : Prop :=
  ∃ t ≤ k, ∃ held : List N, Run ptr a b t held ∧ target ∈ held

/-- The list structure `ptr`, in which the tree vertex `v` is represented by the node `rep v`,
answers every nca query on two leaves in `k` steps: for all leaves `x`, `y`, a run of at most `k`
steps from `rep x`, `rep y` reaches the node `rep (nca x y)` representing their nearest common
ancestor. -/
def AnswersLeafQueriesIn {N : Type*} {h : ℕ} (ptr : N → Fin 2 → Option N) (rep : Vertex h → N)
    (k : ℕ) : Prop :=
  ∀ x y : Vertex h, IsLeaf x → IsLeaf y → AnsweredIn ptr (rep x) (rep y) (rep (nca x y)) k

/-- `A_x` (proof of Theorem 1, p. 340): the tree vertices whose representing nodes are accessible
from the node representing `x` in `k` steps or less. -/
def A {N : Type*} {h : ℕ} (ptr : N → Fin 2 → Option N) (rep : Vertex h → N) (k : ℕ)
    (x : Vertex h) : Set (Vertex h) :=
  {t | rep t ∈ acc ptr k (rep x)}

end HarelTarjan.PointerLB
