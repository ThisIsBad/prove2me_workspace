import Mathlib

namespace ChvatalArtGallery.FanPartition

/-!
Combinatorial n-triangulations (Chvátal 1975, p. 39).

The vertices of the n-gon are `Fin n`, 0-based, in their cyclic (boundary) order: the bounding
n-gon is `0 → 1 → ⋯ → n - 1 → 0`. A planar graph with one face bounded by this n-gon and every
other face a triangle is encoded by its set `D` of inner edges: a maximal set of pairwise
non-crossing diagonals of the n-gon.
-/

/-- Forward cyclic distance from `a` to `b` on the n-cycle: the number of boundary steps
`a → a + 1 → ⋯ → b`, a number in `{0, …, n - 1}`. -/
def cdist {n : ℕ} (a b : Fin n) : ℕ := (b.val + n - a.val) % n

/-- The vertex `j + i` (indices mod n). -/
def shift {n : ℕ} (j : Fin n) (i : ℕ) : Fin n :=
  ⟨(j.val + i) % n, Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le _) j.isLt)⟩

/-- `e` is a side of the n-gon: `e = s(a, a + 1)` for some vertex `a`. -/
def IsBoundaryEdge {n : ℕ} (e : Sym2 (Fin n)) : Prop :=
  ∃ a b : Fin n, e = s(a, b) ∧ cdist a b = 1

/-- `e` is a diagonal of the n-gon: it joins two distinct vertices and is not a side. -/
def IsDiagonal {n : ℕ} (e : Sym2 (Fin n)) : Prop :=
  ∀ a b : Fin n, e = s(a, b) → a ≠ b ∧ cdist a b ≠ 1 ∧ cdist b a ≠ 1

/-- Two chords `e = s(a, b)` and `f = s(c, d)` cross: their four endpoints are distinct and
exactly one of `c, d` lies strictly inside the boundary arc from `a` to `b`. Chords sharing an
endpoint never cross. -/
def Crosses {n : ℕ} (e f : Sym2 (Fin n)) : Prop :=
  ∃ a b c d : Fin n, e = s(a, b) ∧ f = s(c, d) ∧
    0 < cdist a c ∧ cdist a c < cdist a b ∧ cdist a b < cdist a d

/-- `D` is the set of inner edges of an n-triangulation: an n-gon has at least three vertices,
every member is a diagonal, no two members cross, and `D` is maximal (every diagonal crossing
no member of `D` belongs to `D`). -/
def IsTriangulation (n : ℕ) (D : Finset (Sym2 (Fin n))) : Prop :=
  3 ≤ n ∧ (∀ e ∈ D, IsDiagonal e) ∧
  (∀ e ∈ D, ∀ f ∈ D, ¬ Crosses e f) ∧
  (∀ e : Sym2 (Fin n), IsDiagonal e → (∀ f ∈ D, ¬ Crosses e f) → e ∈ D)

/-- The edges of the graph `G` with inner-edge set `D`: the sides of the n-gon and `D`. -/
def IsEdge {n : ℕ} (D : Finset (Sym2 (Fin n))) (e : Sym2 (Fin n)) : Prop :=
  IsBoundaryEdge e ∨ e ∈ D

instance {n : ℕ} (e : Sym2 (Fin n)) : Decidable (IsBoundaryEdge e) := by
  unfold IsBoundaryEdge; infer_instance

instance {n : ℕ} (e : Sym2 (Fin n)) : Decidable (IsDiagonal e) := by
  unfold IsDiagonal; infer_instance

instance {n : ℕ} (e f : Sym2 (Fin n)) : Decidable (Crosses e f) := by
  unfold Crosses; infer_instance

instance {n : ℕ} (D : Finset (Sym2 (Fin n))) (e : Sym2 (Fin n)) : Decidable (IsEdge D e) := by
  unfold IsEdge; infer_instance

instance {n : ℕ} (D : Finset (Sym2 (Fin n))) : Decidable (IsTriangulation n D) := by
  unfold IsTriangulation; infer_instance

/-- The triangles of `G`: the 3-element vertex sets all three of whose pairs are edges of `G`.
In a triangulated polygon these are exactly the bounded (triangular) faces. -/
def triangles (n : ℕ) (D : Finset (Sym2 (Fin n))) : Finset (Finset (Fin n)) :=
  (Finset.univ.powersetCard 3).filter (fun T => ∀ a ∈ T, ∀ b ∈ T, a ≠ b → IsEdge D s(a, b))

/-- Two distinct triangles are adjacent when they share two vertices (hence an edge). -/
def Adjacent {n : ℕ} (T T' : Finset (Fin n)) : Prop :=
  T ≠ T' ∧ (T ∩ T').card = 2

instance {n : ℕ} (T T' : Finset (Fin n)) : Decidable (Adjacent T T') := by
  unfold Adjacent; infer_instance

/-- A set `F` of triangles is dual-connected: every nonempty subset of `F` that is closed under
adjacency inside `F` is all of `F` (equivalently, any two members of `F` are joined by a chain
in `F` whose consecutive members share an edge). -/
def DualConnected {n : ℕ} (F : Finset (Finset (Fin n))) : Prop :=
  ∀ S ⊆ F, S.Nonempty → (∀ X ∈ S, ∀ Y ∈ F, Adjacent X Y → Y ∈ S) → S = F

-- The decision procedures below run through the finsets themselves (`Finset.decidableDforallFinset`),
-- not through the ambient finite types of sets of triangles.
instance {n : ℕ} (F : Finset (Finset (Fin n))) : Decidable (DualConnected F) :=
  @decidable_of_iff _ _
    (by simp only [DualConnected, Finset.mem_powerset])
    (@Finset.decidableDforallFinset _ F.powerset
      (fun S _ => S.Nonempty → (∀ X ∈ S, ∀ Y ∈ F, Adjacent X Y → Y ∈ S) → S = F)
      (fun S _ => @instDecidableForall _ _ inferInstance
        (@instDecidableForall _ _
          (@Finset.decidableDforallFinset _ S (fun X _ => ∀ Y ∈ F, Adjacent X Y → Y ∈ S)
            (fun X _ => @Finset.decidableDforallFinset _ F (fun Y _ => Adjacent X Y → Y ∈ S)
              (fun _ _ => inferInstance)))
          inferInstance)))

/-- `F` is a fan of the n-triangulation with inner edges `D`: a nonempty, dual-connected set of
triangles of `G` (so its union is a k-triangulation with `k = |F| + 2`) having a vertex `c` that
meets all of its inner edges, an inner edge of `F` being an edge shared by two distinct
triangles of `F`. -/
def IsFan (n : ℕ) (D : Finset (Sym2 (Fin n))) (F : Finset (Finset (Fin n))) : Prop :=
  F ⊆ triangles n D ∧ F.Nonempty ∧ DualConnected F ∧
  ∃ c : Fin n, ∀ T ∈ F, ∀ T' ∈ F, Adjacent T T' → c ∈ T ∩ T'

instance (n : ℕ) (D : Finset (Sym2 (Fin n))) (F : Finset (Finset (Fin n))) :
    Decidable (IsFan n D F) := by
  unfold IsFan
  exact @instDecidableAnd _ _ inferInstance (@instDecidableAnd _ _ inferInstance
    (@instDecidableAnd _ _ inferInstance
      (@Fintype.decidableExistsFintype _ _ (fun c =>
        @Finset.decidableDforallFinset _ F (fun T _ => ∀ T' ∈ F, Adjacent T T' → c ∈ T ∩ T')
          (fun T _ => @Finset.decidableDforallFinset _ F (fun T' _ => Adjacent T T' → c ∈ T ∩ T')
            (fun _ _ => inferInstance))) _)))

/-- `P` partitions the n-triangulation with inner edges `D` into fans: every member of `P` is a
fan, distinct members share no triangle, and together they contain every triangle of `G`.
Fans may share vertices and edges. -/
def IsFanPartition (n : ℕ) (D : Finset (Sym2 (Fin n)))
    (P : Finset (Finset (Finset (Fin n)))) : Prop :=
  (∀ F ∈ P, IsFan n D F) ∧
  (∀ F ∈ P, ∀ F' ∈ P, F ≠ F' → Disjoint F F') ∧
  P.biUnion id = triangles n D

instance (n : ℕ) (D : Finset (Sym2 (Fin n))) (P : Finset (Finset (Finset (Fin n)))) :
    Decidable (IsFanPartition n D P) := by
  unfold IsFanPartition
  exact @instDecidableAnd _ _
    (@Finset.decidableDforallFinset _ P (fun F _ => IsFan n D F) (fun _ _ => inferInstance))
    (@instDecidableAnd _ _
      (@Finset.decidableDforallFinset _ P (fun F _ => ∀ F' ∈ P, F ≠ F' → Disjoint F F')
        (fun F _ => @Finset.decidableDforallFinset _ P (fun F' _ => F ≠ F' → Disjoint F F')
          (fun _ _ => inferInstance)))
      inferInstance)

/-- The vertices `j, j + 1, …, j + m - 1` (mod n) of the n-gon, relabelled `0, …, m - 1`. -/
def arc {n : ℕ} (j : Fin n) (m : ℕ) : Fin m → Fin n := fun i => shift j i.val

/-- Pull a set of inner edges of the n-gon back along a relabelling `ι : Fin m → Fin n`: the
diagonals of the m-gon whose image under `ι` lies in `D`. -/
def pullback {m n : ℕ} (ι : Fin m → Fin n) (D : Finset (Sym2 (Fin n))) :
    Finset (Sym2 (Fin m)) :=
  Finset.univ.filter (fun e => IsDiagonal e ∧ Sym2.map ι e ∈ D)

end ChvatalArtGallery.FanPartition
