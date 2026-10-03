import Mathlib

namespace Disjunctive.GeneralDisjunctions

/-- The extreme-ray direction `r^j` of the LP cone `C(J)` at a basic solution with basic index
set `I` and tableau coefficients `ā` (restated from `01-intro-duality`, Balas §1.2, p. 3): for
`i ∈ I`, `r^j_i = -ā_{ij}`; `r^j_j = 1`; and `r^j_i = 0` for `i ∈ J \ {j}`. -/
def extremeRay {ι : Type*} [DecidableEq ι] (I : Finset ι) (abar : ι → ι → ℝ) (j : ι) : ι → ℝ :=
  fun i => if i = j then 1 else if i ∈ I then -abar i j else 0

/-- A convex set `S` is `P_I`-free at `x̄` (restated from `01-intro-duality`, Balas §1.2, p. 4):
`x̄ ∈ int S` and `int S` contains no point of `P_I`. -/
def PIFree {ι : Type*} [Fintype ι] (S : Set (ι → ℝ)) (PI : Set (ι → ℝ)) (xbar : ι → ℝ) : Prop :=
  Convex ℝ S ∧ xbar ∈ interior S ∧ interior S ∩ PI = ∅

open Classical in
/-- The dimension of a polyhedron (or any set) `P` in a real vector space `E`: the dimension of
the linear span of its difference set, i.e. of its affine hull (restated from `02b-polarity`,
Balas §2.2.2, p. 29, `dim(Q)`). -/
noncomputable def PolyDim {E : Type*} [AddCommGroup E] [Module ℝ E] (P : Set E) : ℤ :=
  if P.Nonempty then (Module.finrank ℝ (vectorSpan ℝ P) : ℤ) else -1

/-- `F` is a facet of `Q`: a proper extreme subset (face) of codimension exactly `1` (restated
from `02b-polarity`, Balas §2.2.3, p. 30, used implicitly via "`dim(FQ) = dim(Q) - 1`" for a
facet `FQ` of `Q`).  Dimensions are carried in `ℤ` with
`dim ∅ = -1`: with `ℕ` and truncated subtraction the empty set is a facet of every
one-dimensional polyhedron and a point is a facet of itself. A facet is also required to be
nonempty; properness then follows from the dimension drop. -/
def IsFacet {E : Type*} [AddCommGroup E] [Module ℝ E] (Q F : Set E) : Prop :=
  IsExtreme ℝ Q F ∧ F.Nonempty ∧ PolyDim F = PolyDim Q - 1

/-- `v` is an extreme ray of a cone `W` in a real vector space `E` (restated from `02b-polarity`,
Balas §2.2, p. 27, `extr W`). -/
def IsExtremeRay {E : Type*} [AddCommGroup E] [Module ℝ E] (W : Set E) (v : E) : Prop :=
  v ≠ 0 ∧ v ∈ W ∧ IsExtreme ℝ W {x | ∃ t : ℝ, 0 ≤ t ∧ x = t • v}

/-- `dir` is an extreme-ray direction of the polyhedron `CK` at the apex `v` (Balas §11.3, p.
152): an extreme ray of the recentered cone `{y : v + y ∈ CK}`. -/
def IsExtremeRayAt {n : ℕ} (CK : Set (Fin n → ℝ)) (v dir : Fin n → ℝ) : Prop :=
  IsExtremeRay {y | v + y ∈ CK} dir

/-- The intersection cut `∑_{j∈J} (1/λ_j) x_j ≥ 1` (restated from `01-intro-duality`'s Theorem
1.1, as a set), for a nonbasic index set `J` and exit parameters `λ_j`. -/
def IntersectionCutSet {ι : Type*} (J : Finset ι) (lam : ι → ℝ) : Set (ι → ℝ) :=
  {x | 1 ≤ ∑ j ∈ J, (lam j)⁻¹ * x j}

end Disjunctive.GeneralDisjunctions
