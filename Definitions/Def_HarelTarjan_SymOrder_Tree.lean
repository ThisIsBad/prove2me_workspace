import Mathlib

namespace HarelTarjan.SymOrder

/-- The vertices of the complete binary tree `T` of depth `d` (Harel–Tarjan, §3, p. 341, Fig. 1;
Appendix, pp. 354–355). A vertex is the path from the root to it, written as a list of turns
(`false` = go to the left child, `true` = go to the right child), of length at most `d`. The root is
`[]`, the children of `s` are `s ++ [false]` (left) and `s ++ [true]` (right), and the depth of `s`
is its length. There are `2 ^ (d + 1) - 1` vertices. -/
abbrev Vertex (d : ℕ) : Type := {s : List Bool // s.length ≤ d}

/-- The finite set of all lists of booleans of length at most `d`. -/
def pathsUpTo (d : ℕ) : Finset (List Bool) :=
  (Finset.range (d + 1)).biUnion fun k =>
    (Finset.univ : Finset (List.Vector Bool k)).image List.Vector.toList

theorem mem_pathsUpTo {d : ℕ} (s : List Bool) : s ∈ pathsUpTo d ↔ s.length ≤ d := by
  simp only [pathsUpTo, Finset.mem_biUnion, Finset.mem_range, Finset.mem_image,
    Finset.mem_univ, true_and]
  constructor
  · rintro ⟨k, hk, x, rfl⟩
    rw [List.Vector.toList_length]; omega
  · intro hs
    exact ⟨s.length, by omega, ⟨s, rfl⟩, rfl⟩

instance (d : ℕ) : Fintype (Vertex d) :=
  Fintype.subtype (pathsUpTo d) mem_pathsUpTo

/-- The depth of a vertex: the length of the path from it to the root. -/
def depth {d : ℕ} (v : Vertex d) : ℕ := v.1.length

/-- The height of a vertex `v` of the complete binary tree of depth `d`: the length of the longest
path from a leaf to `v`. In a complete binary tree every leaf has depth `d`, so this is
`d - depth v` (no truncation: `depth v ≤ d`). -/
def height {d : ℕ} (v : Vertex d) : ℕ := d - v.1.length

/-- `w` is an ancestor of `v` (and `v` a descendant of `w`) in the Appendix's sense
`p^i(v) = w` for some `i ≥ 0`: the path to `w` is a prefix of the path to `v`. Every vertex is an
ancestor and a descendant of itself. -/
def IsAncestor {d : ℕ} (w v : Vertex d) : Prop := w.1 <+: v.1

/-- Two vertices are unrelated if neither is an ancestor of the other (Appendix, p. 354). -/
def Unrelated {d : ℕ} (v w : Vertex d) : Prop := ¬ IsAncestor v w ∧ ¬ IsAncestor w v

/-- The longest common prefix of two lists of booleans. -/
def lcp : List Bool → List Bool → List Bool
  | a :: s, b :: t => if a = b then a :: lcp s t else []
  | _, _ => []

theorem lcp_length_le_left : ∀ s t : List Bool, (lcp s t).length ≤ s.length
  | a :: s, b :: t => by
    unfold lcp
    split_ifs
    · simpa using lcp_length_le_left s t
    · simp
  | [], _ => by simp [lcp]
  | _ :: _, [] => by simp [lcp]

/-- The nearest common ancestor `nca(v, w)`: the vertex whose path is the longest common prefix of
the paths to `v` and `w`, i.e. the vertex of greatest depth that is an ancestor of both
(Appendix, p. 355). -/
def nca {d : ℕ} (v w : Vertex d) : Vertex d :=
  ⟨lcp v.1 w.1, (lcp_length_le_left v.1 w.1).trans v.2⟩

/-- The ancestor of `v` at depth `k` (for `k ≤ depth v`): the vertex whose path is the first `k`
turns of the path to `v`. -/
def ancestorAtDepth {d : ℕ} (v : Vertex d) (k : ℕ) : Vertex d :=
  ⟨v.1.take k, by rw [List.length_take]; exact (Nat.min_le_right _ _).trans v.2⟩

/-- The left-to-right position (counting from `0`) of `v` among the `2 ^ depth v` vertices of its
depth: the path to `v` read as a binary numeral, most significant turn first, with
`false` = `0` (left) and `true` = `1` (right). -/
def leftIndex {d : ℕ} (v : Vertex d) : ℕ :=
  v.1.foldl (fun acc b => 2 * acc + if b then 1 else 0) 0

end HarelTarjan.SymOrder
