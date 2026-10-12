import Mathlib

namespace NestedLogitVariants.General

/-- An instance of the assortment problem of §1 (pp. 6–8): nests `ι` (the paper's `M`), products
`Fin n` (the paper's `N = {1, …, n}`, here `0, …, n-1`), the no-nest weight `v0` (`v_0`), the
within-nest no-purchase weights `vnp i` (`v_{i0}`), the preference weights `v i j` (`v_{ij}`), the
revenues `r i j` (`r_{ij}`) and the dissimilarity parameters `γ i` (`γ_i`). -/
structure Instance (ι : Type*) (n : ℕ) where
  v0 : ℝ
  vnp : ι → ℝ
  v : ι → Fin n → ℝ
  r : ι → Fin n → ℝ
  γ : ι → ℝ

/-- The standing assumptions of §1 (pp. 6–7): nonnegative no-purchase weights `v_0, v_{i0} ≥ 0`,
revenues ordered `r_{i1} ≥ … ≥ r_{in}` within each nest, together with the disclosed pins
`v_{ij} > 0`, `r_{ij} ≥ 0` and `γ_i > 0` (the page has `γ_i ≥ 0`). -/
structure Instance.Standing {ι : Type*} {n : ℕ} (I : Instance ι n) : Prop where
  v0_nonneg : 0 ≤ I.v0
  vnp_nonneg : ∀ i, 0 ≤ I.vnp i
  v_pos : ∀ i j, 0 < I.v i j
  r_nonneg : ∀ i j, 0 ≤ I.r i j
  γ_pos : ∀ i, 0 < I.γ i
  r_antitone : ∀ i, Antitone (I.r i)

variable {ι : Type*} {n : ℕ}

/-- `V_i(S) = v_{i0} + ∑_{j ∈ S} v_{ij}`, the total preference weight in nest `i` when `S` is
offered there. -/
def V (I : Instance ι n) (i : ι) (S : Finset (Fin n)) : ℝ := I.vnp i + ∑ j ∈ S, I.v i j

/-- `R_i(S) = ∑_{j ∈ S} r_{ij} v_{ij} / V_i(S)`, the expected revenue from nest `i` given that the
customer chose it; `R_i(∅) = 0` because the numerator is `0` (and `x / 0 = 0`). -/
noncomputable def R (I : Instance ι n) (i : ι) (S : Finset (Fin n)) : ℝ :=
  (∑ j ∈ S, I.r i j * I.v i j) / V I i S

/-- `V_i(S)^{γ_i}` (`Real.rpow`), the attractiveness of nest `i`. -/
noncomputable def nestWeight (I : Instance ι n) (i : ι) (S : Finset (Fin n)) : ℝ := V I i S ^ I.γ i

/-- `Π(S_1, …, S_m) = ∑_i Q_i(S_1, …, S_m) R_i(S_i)` with `Q_i` from (1):
`Q_i = V_i(S_i)^{γ_i} / (v_0 + ∑_l V_l(S_l)^{γ_l})`. -/
noncomputable def revenue [Fintype ι] (I : Instance ι n) (S : ι → Finset (Fin n)) : ℝ :=
  (∑ i, nestWeight I i (S i) * R I i (S i)) / (I.v0 + ∑ i, nestWeight I i (S i))

/-- `S` is an optimal solution of problem (2): `Π(S) ≥ Π(S')` for every assortment `S'`. -/
def IsOptimal [Fintype ι] (I : Instance ι n) (S : ι → Finset (Fin n)) : Prop :=
  ∀ S' : ι → Finset (Fin n), revenue I S' ≤ revenue I S

/-- The nested-by-revenue assortment `N_ij = {1, …, j}` (`N_i0 = ∅`), here `{k | k < j}`; it does not
depend on the nest. -/
def nbr (n j : ℕ) : Finset (Fin n) := Finset.univ.filter (fun k => k.val < j)

/-- `(x, y)` is feasible for the linear program (3):
`v_0 x ≥ ∑_i y_i` and `y_i ≥ V_i(S)^{γ_i} (R_i(S) − x)` for every `S ⊂ N` and every nest `i`. -/
def LP3Feasible [Fintype ι] (I : Instance ι n) (x : ℝ) (y : ι → ℝ) : Prop :=
  (∑ i, y i) ≤ I.v0 * x ∧ ∀ i (S : Finset (Fin n)), nestWeight I i S * (R I i S - x) ≤ y i

/-- `(x, y)` is feasible for the linear program (4) with candidate collections `A i`
(the paper's `{A_it : t ∈ T_i}`): the second constraint of (3) only for `S ∈ A i`. -/
def LP4Feasible [Fintype ι] (I : Instance ι n) (A : ι → Set (Finset (Fin n))) (x : ℝ) (y : ι → ℝ) :
    Prop :=
  (∑ i, y i) ≤ I.v0 * x ∧ ∀ i, ∀ S ∈ A i, nestWeight I i S * (R I i S - x) ≤ y i

/-- `(x, y)` is an optimal solution of (4): feasible, and `x` is minimal among feasible points. -/
def LP4Optimal [Fintype ι] (I : Instance ι n) (A : ι → Set (Finset (Fin n))) (x : ℝ) (y : ι → ℝ) :
    Prop :=
  LP4Feasible I A x y ∧ ∀ x' y', LP4Feasible I A x' y' → x ≤ x'

end NestedLogitVariants.General
