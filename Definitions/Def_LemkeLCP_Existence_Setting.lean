import Mathlib
open Matrix

namespace LemkeLCP.Existence

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The set `Z` of (1), Lemke 1965, p. 2: `Z = {z : Mz − w = q, z ≥ 0, w ≥ 0}`, where
`w = Mz − q` always defines `w` (p. 2). -/
def Z (M : Matrix ι ι ℝ) (q : ι → ℝ) : Set (ι → ℝ) :=
  {z | 0 ≤ z ∧ 0 ≤ M *ᵥ z - q}

/-- Def. 1, p. 2: an equilibrium point is a point of `Z` with `zᵀw = 0`, `w = Mz − q`. -/
def IsEquilibriumPoint (M : Matrix ι ι ℝ) (q : ι → ℝ) (z : ι → ℝ) : Prop :=
  z ∈ Z M q ∧ z ⬝ᵥ (M *ᵥ z - q) = 0

/-- The set `S` of all equilibrium points of `Z` (p. 3, after Def. 5). -/
def S (M : Matrix ι ι ℝ) (q : ι → ℝ) : Set (ι → ℝ) :=
  {z | IsEquilibriumPoint M q z}

/-- The columns of `N(z)` (p. 2): from `(Mᵀ, I)` delete `(Mᵀ)ᵢ` iff `(w)ᵢ ≠ 0` and `(I)ᵢ` iff
`(z)ᵢ ≠ 0`. The kept column `(Mᵀ)ᵢ` is indexed by `Sum.inl i`, the kept `(I)ᵢ` by `Sum.inr i`. -/
def Ncols (M : Matrix ι ι ℝ) (q : ι → ℝ) (z : ι → ℝ) :
    {i // (M *ᵥ z - q) i = 0} ⊕ {i // z i = 0} → (ι → ℝ)
  | Sum.inl i => fun j => M i.1 j
  | Sum.inr i => Pi.single i.1 1

/-- `rank N(z)`: the dimension of the span of the columns of `N(z)`. -/
noncomputable def rankN (M : Matrix ι ι ℝ) (q : ι → ℝ) (z : ι → ℝ) : ℕ :=
  Module.finrank ℝ (Submodule.span ℝ (Set.range (Ncols M q z)))

/-- Def. 2, p. 2: `z` is an extreme point of `Z` iff `z ∈ Z` and `rank N(z) = n`. -/
def IsExtremePoint (M : Matrix ι ι ℝ) (q : ι → ℝ) (z : ι → ℝ) : Prop :=
  z ∈ Z M q ∧ rankN M q z = Fintype.card ι

/-- Def. 2, p. 2: `z` lies on an open edge of `Z` iff `z ∈ Z` and `rank N(z) = n − 1`
(written `rank N(z) + 1 = n`, so that no truncated subtraction occurs). -/
def OnOpenEdge (M : Matrix ι ι ℝ) (q : ι → ℝ) (z : ι → ℝ) : Prop :=
  z ∈ Z M q ∧ rankN M q z + 1 = Fintype.card ι

/-- Def. 3, p. 2: `Z` is non-degenerate iff for every `z ∈ Rₙ` the columns of `N(z)` are
linearly independent (number of columns = rank). -/
def NonDegenerate (M : Matrix ι ι ℝ) (q : ι → ℝ) : Prop :=
  ∀ z : ι → ℝ, LinearIndependent ℝ (Ncols M q z)

/-- Which columns `N(z)` keeps: the indices with `(w)ᵢ = 0` and those with `(z)ᵢ = 0`.
`N(z) = N(z')` iff the zero patterns of `z` and `z'` agree. -/
def zeroPattern (M : Matrix ι ι ℝ) (q : ι → ℝ) (z : ι → ℝ) : Set ι × Set ι :=
  ({i | (M *ᵥ z - q) i = 0}, {i | z i = 0})

/-- An open edge of `Z` (p. 3): the set of points `z ∈ Z` with a given `N(z)`, where that
`N(z)` is the one of a point lying on an open edge. -/
def IsOpenEdge (M : Matrix ι ι ℝ) (q : ι → ℝ) (E : Set (ι → ℝ)) : Prop :=
  ∃ z₀, OnOpenEdge M q z₀ ∧ E = {z | z ∈ Z M q ∧ zeroPattern M q z = zeroPattern M q z₀}

/-- A closed edge of `Z`: the closure of an open edge (p. 3). -/
def IsClosedEdge (M : Matrix ι ι ℝ) (q : ι → ℝ) (C : Set (ι → ℝ)) : Prop :=
  ∃ E, IsOpenEdge M q E ∧ C = closure E

/-- A ray of `Z` (p. 3): an edge having just one end-point; the end-points of an open edge `E`
are the points of `closure E` not in `E`. -/
def IsRay (M : Matrix ι ι ℝ) (q : ι → ℝ) (E : Set (ι → ℝ)) : Prop :=
  IsOpenEdge M q E ∧ ∃ p, closure E \ E = {p}

/-- Def. 5, (4), p. 3: `Zₛ = {z ∈ Z : zᵀw = (z)ₛ(w)ₛ}`. -/
def Zs (M : Matrix ι ι ℝ) (q : ι → ℝ) (s : ι) : Set (ι → ℝ) :=
  {z | z ∈ Z M q ∧ z ⬝ᵥ (M *ᵥ z - q) = z s * (M *ᵥ z - q) s}

/-- Def. 4, p. 3: an adjacency path is a non-empty class `𝒞` of closed edges of `Z` whose union
is connected and such that no three distinct edges of the class intersect. The path as a set
is `⋃₀ 𝒞`. -/
def IsAdjacencyPath (M : Matrix ι ι ℝ) (q : ι → ℝ) (𝒞 : Set (Set (ι → ℝ))) : Prop :=
  𝒞.Nonempty ∧ (∀ C ∈ 𝒞, IsClosedEdge M q C) ∧ IsConnected (⋃₀ 𝒞) ∧
    ∀ C₁ ∈ 𝒞, ∀ C₂ ∈ 𝒞, ∀ C₃ ∈ 𝒞, C₁ ≠ C₂ → C₁ ≠ C₃ → C₂ ≠ C₃ → C₁ ∩ C₂ ∩ C₃ = ∅

/-- p. 3: an end-point of an adjacency path is an extreme point of `Z` meeting exactly one
edge of the path. -/
def IsPathEndPoint (M : Matrix ι ι ℝ) (q : ι → ℝ) (𝒞 : Set (Set (ι → ℝ))) (z : ι → ℝ) :
    Prop :=
  IsExtremePoint M q z ∧ ∃! C, C ∈ 𝒞 ∧ z ∈ C

/-- Conditions (i)–(ii) of Theorem 4, p. 7: for every `u ≥ 0`, (i) `uᵀMu ≥ 0`, and
(ii) `uᵀMu = 0` implies (21) `Mu + Mᵀu = 0` (later called *copositive-plus*). -/
def CopositivePlus (M : Matrix ι ι ℝ) : Prop :=
  ∀ u : ι → ℝ, 0 ≤ u → 0 ≤ u ⬝ᵥ (M *ᵥ u) ∧ (u ⬝ᵥ (M *ᵥ u) = 0 → M *ᵥ u + Mᵀ *ᵥ u = 0)

/-- (9), p. 5: `Z* = {(z, z₀) : Mz + z₀e − w = q, w ≥ 0, z ≥ 0, z₀ ≥ 0}`. -/
def Zstar (M : Matrix ι ι ℝ) (q : ι → ℝ) : Set ((ι → ℝ) × ℝ) :=
  {p | 0 ≤ p.1 ∧ 0 ≤ p.2 ∧ 0 ≤ M *ᵥ p.1 + (fun _ => p.2) - q}

/-- (10), p. 5: `Z₀* = {z* ∈ Z* : zᵀw = 0}`. -/
def Z0star (M : Matrix ι ι ℝ) (q : ι → ℝ) : Set ((ι → ℝ) × ℝ) :=
  {p | p ∈ Zstar M q ∧ p.1 ⬝ᵥ (M *ᵥ p.1 + (fun _ => p.2) - q) = 0}

/-- The bordered matrix of (13), p. 6: `(M e; −eᵀ 0)`, indexed by `ι ⊕ Unit`
(the extra coordinate `Sum.inr ()` is `z₀`). -/
def Mss (M : Matrix ι ι ℝ) : Matrix (ι ⊕ Unit) (ι ⊕ Unit) ℝ :=
  Matrix.fromBlocks M (Matrix.of fun _ _ => 1) (Matrix.of fun _ _ => -1) 0

/-- The bordered right-hand side of (13), p. 6: `(q; −k)`. With it,
`Z** = Z (Mss M) (qss q k)` and `Z₀** = Zs (Mss M) (qss q k) (Sum.inr ())` (14). -/
def qss (q : ι → ℝ) (k : ℝ) : ι ⊕ Unit → ℝ :=
  Sum.elim q (fun _ => -k)

/-- The ray `E₀*` of (11), p. 6, as a set of points `z* = (z, z₀)` of the bordered system (13)
(`Sum.inr ()` is `z₀`): `z = 0` and `z₀ > Maxᵢ (q)ᵢ`, with `w = z₀e − q` the defined `w`.
The clause `z₀ > 0`, which (11) omits, is the constraint `z₀ ≥ 0` of (9) made strict so that the
end-point is not on the open edge. -/
def E0ss (q : ι → ℝ) : Set (ι ⊕ Unit → ℝ) :=
  {p | (∀ i : ι, p (Sum.inl i) = 0) ∧ 0 < p (Sum.inr ()) ∧ ∀ i : ι, q i < p (Sum.inr ())}

end LemkeLCP.Existence
