import Mathlib

namespace HarelTarjan.PointerLB

/-- The vertices of the complete binary tree of height `h` (Harel–Tarjan, §2 and Appendix,
pp. 340, 354–355). A vertex is the path from the root to it, written as a list of turns
(`false` = left child, `true` = right child), of length at most `h`. The root is `[]`, the
children of `w` are `w ++ [false]` and `w ++ [true]`, and the depth of `w` is its length. -/
abbrev Vertex (h : ℕ) : Type := {s : List Bool // s.length ≤ h}

/-- `w` is an ancestor of `v` (and `v` a descendant of `w`), in the Appendix's sense
`p^i(v) = w` for some `i ≥ 0`: the path to `w` is a prefix of the path to `v`. Every vertex is an
ancestor and a descendant of itself. -/
def IsAncestor {h : ℕ} (w v : Vertex h) : Prop := w.1 <+: v.1

/-- `v` is a leaf of the complete binary tree of height `h`: its depth is `h`. -/
def IsLeaf {h : ℕ} (v : Vertex h) : Prop := v.1.length = h

/-- The finite set of the `2 ^ h` leaves (the vertices of depth `h`). -/
def leaves (h : ℕ) : Finset (Vertex h) :=
  (Finset.univ : Finset (List.Vector Bool h)).map
    ⟨fun v : List.Vector Bool h => (⟨v.1, le_of_eq v.2⟩ : Vertex h),
      fun _ _ hab => Subtype.ext (congrArg (fun v : Vertex h => v.1) hab)⟩

/-- The longest common prefix of two lists of turns. -/
def lcp : List Bool → List Bool → List Bool
  | a :: x, b :: y => if a = b then a :: lcp x y else []
  | _, _ => []

/-- The longest common prefix is no longer than its first argument. -/
theorem lcp_length_le_left : ∀ x y : List Bool, (lcp x y).length ≤ x.length
  | a :: x, b :: y => by
      unfold lcp
      split_ifs
      · simpa using lcp_length_le_left x y
      · simp
  | [], _ => by simp [lcp]
  | _ :: _, [] => by simp [lcp]

/-- The nearest common ancestor `nca(x, y)` of two vertices: the vertex whose path is the longest
common prefix of the paths to `x` and `y`, i.e. the vertex of greatest depth that is an ancestor
of both (Appendix, p. 355). -/
def nca {h : ℕ} (x y : Vertex h) : Vertex h :=
  ⟨lcp x.1 y.1, (lcp_length_le_left x.1 y.1).trans x.2⟩

end HarelTarjan.PointerLB
