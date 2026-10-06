import Mathlib

namespace BregmanRelax.Cyclic

/-- Conditions I–IV and VI of §1 (Bregman 1967, pp. 200–201) on the family of sets `A`, the convex
set `S`, the function `D` (meaningful on `S × S`) and the D-projection map `P` of condition II.
`P i y` is the D-projection of `y` onto `A i`. Condition IV is stated in the form the proofs use
(the right derivative at `y` in the direction of a point `w ∈ S` vanishes); "compact" in VI is
sequential compactness. -/
structure DConditions {X : Type*} [AddCommGroup X] [Module ℝ X] [TopologicalSpace X] {ι : Type*}
    (A : ι → Set X) (S : Set X) (D : X → X → ℝ) (P : ι → X → X) : Prop where
  /-- every `A i` is closed -/
  isClosed : ∀ i, IsClosed (A i)
  /-- every `A i` is convex -/
  convex : ∀ i, Convex ℝ (A i)
  /-- `S` is convex -/
  convex_S : Convex ℝ S
  /-- condition I: `D ≥ 0` on `S × S` -/
  nonneg : ∀ x ∈ S, ∀ y ∈ S, 0 ≤ D x y
  /-- condition I: `D x y = 0 ↔ x = y` on `S × S` -/
  eq_zero_iff : ∀ x ∈ S, ∀ y ∈ S, D x y = 0 ↔ x = y
  /-- condition II: `P i y ∈ A i ∩ S` minimizes `D (·) y` over `A i ∩ S` -/
  proj : ∀ i, ∀ y ∈ S, P i y ∈ A i ∩ S ∧ ∀ z ∈ A i ∩ S, D (P i y) y ≤ D z y
  /-- condition III: `z ↦ D z y - D z (P i y)` is convex on `A i ∩ S` -/
  convexOn : ∀ i, ∀ y ∈ S, ConvexOn ℝ (A i ∩ S) (fun z => D z y - D z (P i y))
  /-- condition IV: `D (y + t (w - y)) y / t → 0` as `t → 0⁺`, for `y, w ∈ S` -/
  deriv_zero : ∀ y ∈ S, ∀ w ∈ S,
    Filter.Tendsto (fun t : ℝ => D (y + t • (w - y)) y / t) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0)
  /-- condition VI -/
  conv : ∀ (x y : ℕ → X) (y' : X), (∀ n, x n ∈ S) → (∀ n, y n ∈ S) →
    Filter.Tendsto (fun n => D (x n) (y n)) Filter.atTop (nhds 0) →
    Filter.Tendsto y Filter.atTop (nhds y') → y' ∈ closure S →
    (∃ K : Set X, IsSeqCompact K ∧ ∀ n, x n ∈ K) → Filter.Tendsto x Filter.atTop (nhds y')

/-- Condition V (p. 201), for the points `z ∈ Zv` (in §1, `Zv = R ∩ S`): every sublevel set
`{x ∈ S | D z x ≤ L}` is sequentially compact. -/
def CondV {X : Type*} [TopologicalSpace X] (S : Set X) (D : X → X → ℝ) (Zv : Set X) : Prop :=
  ∀ z ∈ Zv, ∀ L : ℝ, IsSeqCompact {x | x ∈ S ∧ D z x ≤ L}

/-- A relaxation sequence with control `i` (p. 201, steps (1)–(2)):
`x 0 ∈ S` and `x (n+1) = P (i n) (x n)`. -/
def IsRelaxSeq {X : Type*} {ι : Type*} (S : Set X) (P : ι → X → X) (i : ℕ → ι) (x : ℕ → X) :
    Prop :=
  x 0 ∈ S ∧ ∀ n, x (n + 1) = P (i n) (x n)

/-- The cyclic control of Theorem 1 (p. 203), 0-based: `n ↦ n mod m`, i.e. the paper's
`i_n = (n mod m) + 1` shifted by one. -/
def cyclicControl {m : ℕ} (hm : 0 < m) : ℕ → Fin m := fun n => ⟨n % m, Nat.mod_lt n hm⟩

end BregmanRelax.Cyclic
