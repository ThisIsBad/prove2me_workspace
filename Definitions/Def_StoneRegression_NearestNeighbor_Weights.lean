import Mathlib
import Definitions.Def_StoneRegression_Criterion_Setting

namespace StoneRegression.NearestNeighbor

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

/-- A sequence of scales (p. 599): `s n x xs j = s_{n,j+1}(x, x₁, …, xₙ)`, with the StoneRegression.Criterion.sample `xs i = x_{i+1}`
and the coordinates `j` 0-based. -/
abbrev ScaleSeq (d : ℕ) : Type :=
  (n : ℕ) → EuclideanSpace ℝ (Fin d) → (Fin n → EuclideanSpace ℝ (Fin d)) → Fin d → ℝ

/-- The (pseudo) metric (6) of a scale vector `sv`:
`ρ(u, v) = (∑_{j : sv j > 0} ((u_j − v_j)/sv_j)²)^{1/2}`; coordinates with `sv j ≤ 0` are omitted.
`ρₙ` at the data `(x, xs)` is `rho (s n x xs)`. -/
noncomputable def rho {d : ℕ} (sv : Fin d → ℝ) (u v : EuclideanSpace ℝ (Fin d)) : ℝ :=
  Real.sqrt (∑ j ∈ Finset.univ.filter (fun j => 0 < sv j), ((u j - v j) / sv j) ^ 2)

/-- `ν` of (8) (p. 600): `1 + #{l ≠ i : ρ(X_l, X) < ρ(X_i, X)}`, for the metric `rho sv`. -/
noncomputable def nnNu {d n : ℕ} (sv : Fin d → ℝ) (x : EuclideanSpace ℝ (Fin d))
    (xs : Fin n → EuclideanSpace ℝ (Fin d)) (i : Fin n) : ℕ :=
  1 + (Finset.univ.filter fun l => l ≠ i ∧ rho sv (xs l) x < rho sv (xs i) x).card

/-- `λ` of (8) (p. 600): `1 + #{l ≠ i : ρ(X_l, X) = ρ(X_i, X)}`, for the metric `rho sv`. -/
noncomputable def nnLam {d n : ℕ} (sv : Fin d → ℝ) (x : EuclideanSpace ℝ (Fin d))
    (xs : Fin n → EuclideanSpace ℝ (Fin d)) (i : Fin n) : ℕ :=
  1 + (Finset.univ.filter fun l => l ≠ i ∧ rho sv (xs l) x = rho sv (xs i) x).card

/-- The nearest neighbor probability weight function (8) associated with coefficients `c` and scales `s`
(pp. 599–600): `W_{n,i+1}(x) = (c_{n,ν} + ⋯ + c_{n,ν+λ−1}) / λ`, ties in `ρₙ` being averaged over the tied
ranks. **The coefficients keep the paper's 1-based index**: `c n m` is `c_{n,m}` for `m ≥ 1`; `c n 0` is
never read (`ν ≥ 1`). The StoneRegression.Criterion.sample index `i : Fin n` is 0-based and stands for the paper's `i + 1`. -/
noncomputable def nnWeights {d : ℕ} (c : ℕ → ℕ → ℝ) (s : ScaleSeq d) : StoneRegression.Criterion.WeightSeq d :=
  fun n x xs i =>
    (∑ m ∈ Finset.Ico (nnNu (s n x xs) x xs i) (nnNu (s n x xs) x xs i + nnLam (s n x xs) x xs i), c n m) /
      (nnLam (s n x xs) x xs i : ℝ)

/-- A coefficient row `c_n` (p. 599): `c_{n1} ≥ ⋯ ≥ c_{nn} ≥ 0`, `c_{ni} = 0` for `i > n`, and
`c_{n1} + ⋯ + c_{nn} = 1` (1-based index). -/
def IsCoeffRow (c : ℕ → ℕ → ℝ) (n : ℕ) : Prop :=
  (∀ i j, 1 ≤ i → i ≤ j → j ≤ n → c n j ≤ c n i) ∧ 0 ≤ c n n ∧ (∀ i, n < i → c n i = 0) ∧
    ∑ i ∈ Finset.Icc 1 n, c n i = 1

/-- "The `j`th coordinate of `X` has a nondegenerate distribution" (p. 599): the law of `X_j` is not a
point mass. -/
def CoordNondeg {d : ℕ} (μ : Measure (EuclideanSpace ℝ (Fin d))) (j : Fin d) : Prop :=
  ∀ t : ℝ, μ {x | x j = t} < 1

/-- Boundedness in probability (p. 598): `lim_{M→∞} limsupₙ P(|Zₙ| ≥ M) = 0` (the `limsup` in `ℝ≥0∞`). -/
def BoundedInProb {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (Z : ℕ → Ω → ℝ) : Prop :=
  Tendsto (fun M : ℝ => limsup (fun n => P {ω | M ≤ |Z n ω|}) atTop) atTop (𝓝 0)

/-- Condition (7) with constants `a, b` (p. 599), read for all points: whenever `n ≥ 1`, `1 ≤ i ≤ n`,
`1 ≤ j ≤ d` and the `j`th coordinates of `x₁, …, xₙ` are not all equal,
`a·s_{nj}(xᵢ, x₁, …, x, …, xₙ) ≤ s_{nj}(x, x₁, …, xₙ) ≤ b·s_{nj}(xᵢ, x₁, …, x, …, xₙ)`.
`(xs i, Function.update xs i x)` is the sequence with `x` and `xᵢ` interchanged. -/
def Cond7 {d : ℕ} (s : ScaleSeq d) (a b : ℝ) : Prop :=
  ∀ n, 1 ≤ n → ∀ (x : EuclideanSpace ℝ (Fin d)) (xs : Fin n → EuclideanSpace ℝ (Fin d)) (i : Fin n)
    (j : Fin d), (∃ k l, xs k j ≠ xs l j) →
      a * s n (xs i) (Function.update xs i x) j ≤ s n x xs j ∧
        s n x xs j ≤ b * s n (xs i) (Function.update xs i x) j

/-- A regular sequence of scales with constants `0 < a ≤ b` (p. 599): each `s n` is Borel (added,
disclosed) and nonnegative; `P(s_{nj} > 0) → 1` for every coordinate with a nondegenerate distribution;
`s_{nj}/s_{nl}` is bounded in probability for every two such coordinates (real division, `0` where
`s_{nl} = 0`); and (7) holds. -/
def IsRegular {d : ℕ} (μ : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure μ] (s : ScaleSeq d)
    (a b : ℝ) : Prop :=
  (∀ n, Measurable (fun p : EuclideanSpace ℝ (Fin d) × (Fin n → EuclideanSpace ℝ (Fin d)) => s n p.1 p.2)) ∧
  (∀ n x xs j, 0 ≤ s n x xs j) ∧
  (∀ j, CoordNondeg μ j →
    Tendsto (fun n => StoneRegression.Criterion.xLaw μ {ω | 0 < s n (ω 0) (StoneRegression.Criterion.sample ω n) j}) atTop (𝓝 1)) ∧
  (∀ j l, CoordNondeg μ j → CoordNondeg μ l →
    BoundedInProb (StoneRegression.Criterion.xLaw μ) (fun n ω => s n (ω 0) (StoneRegression.Criterion.sample ω n) j / s n (ω 0) (StoneRegression.Criterion.sample ω n) l)) ∧
  0 < a ∧ a ≤ b ∧ Cond7 s a b

/-- `I_{n,t}(x)` (p. 599 and p. 611): the indices `i` such that fewer than `⌊t⌋` of the points `x₁, …, xₙ`
are strictly closer to `x` than `xᵢ` in the metric `rho sv`. For `k ≤ t < k + 1` this is `I_{nk}(x)`, and
for `0 ≤ t < 1` it is empty, which is `I_{n0}(x) = ∅`. -/
noncomputable def nearIdx {d n : ℕ} (sv : Fin d → ℝ) (x : EuclideanSpace ℝ (Fin d))
    (xs : Fin n → EuclideanSpace ℝ (Fin d)) (t : ℝ) : Finset (Fin n) :=
  Finset.univ.filter fun i => (Finset.univ.filter fun l => rho sv (xs l) x < rho sv (xs i) x).card < ⌊t⌋₊

/-- The family `𝒱(d, c)` (p. 612): sets `V ⊆ ℝᵈ` such that any two nonzero `u, v ∈ V` satisfy
`u·v > (1 − c²/2)‖u‖‖v‖`. The page defines it for `0 < c ≤ 1`. -/
def ConeFamily (d : ℕ) (c : ℝ) : Set (Set (EuclideanSpace ℝ (Fin d))) :=
  {V | ∀ u ∈ V, ∀ v ∈ V, u ≠ 0 → v ≠ 0 → (1 - c ^ 2 / 2) * (‖u‖ * ‖v‖) < inner ℝ u v}

/-- `β(d, c)` (p. 612): the minimum cardinality of a subcollection of `𝒱(d, c)` covering `ℝᵈ`, as an
`sInf` over `ℕ`. For `0 < c ≤ 1` the set is nonempty (the unit sphere is compact, so finitely many cones
cover `ℝᵈ`), hence the `sInf` is the page's minimum; this fact is not proved here and no statement
assumes it (were the set empty, the `sInf` would be `0`). -/
noncomputable def beta (d : ℕ) (c : ℝ) : ℕ :=
  sInf {k | ∃ V : Fin k → Set (EuclideanSpace ℝ (Fin d)), (∀ m, V m ∈ ConeFamily d c) ∧ (⋃ m, V m) = Set.univ}

/-- The swapped weights `U_{n,i+1}(x) = W_{n,i+1}(xᵢ₊₁, x₁, …, x, …, xₙ)` (p. 613): the query is the
`i`th StoneRegression.Criterion.sample point and `x` takes its slot, both in the weights and in the scales. -/
def swapW {d : ℕ} (W : StoneRegression.Criterion.WeightSeq d) : StoneRegression.Criterion.WeightSeq d :=
  fun n x xs i => W n (xs i) (Function.update xs i x) i

/-- Coordinatewise scaling `(coordScale bv u)_j = bv_j · u_j` (Proposition 10's `ũ`, `ṽ`). -/
noncomputable def coordScale {d : ℕ} (bv : Fin d → ℝ) (u : EuclideanSpace ℝ (Fin d)) :
    EuclideanSpace ℝ (Fin d) :=
  WithLp.toLp 2 (fun j => bv j * u j)

end StoneRegression.NearestNeighbor
