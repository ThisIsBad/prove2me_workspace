import Mathlib
import Definitions.Def_Disjunctive_HigherDim_Basic

namespace Disjunctive.HigherDim

/-- `M(K)`, the Lovász-Schrijver lifted polyhedron (Balas §7.2, p. 92-93, eq. (7.4)): a
symmetric matrix `Y` with `Y_{jj} = x_j` for `j ∈ N'`, satisfying the linearized system for
every `j ∈ N'` simultaneously. -/
def MK {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (Nprime : Finset (Fin n)) :
    Set ((Fin n → ℝ) × (Fin n → Fin n → ℝ)) :=
  {p | (∀ i j, p.2 i j = p.2 j i) ∧ (∀ j ∈ Nprime, p.2 j j = p.1 j) ∧
        ∀ j ∈ Nprime, (∀ i, 0 ≤ (A.mulVec p.1) i - (A.mulVec (fun k => p.2 k j)) i + b i * (p.1 j - 1)) ∧
          ∀ i, 0 ≤ (A.mulVec (fun k => p.2 k j)) i - b i * p.1 j}

/-- `N(K)`, the projection of `M(K)` onto the `x`-space (Balas §7.2, p. 93, Step 3). -/
def NOp {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (Nprime : Finset (Fin n)) :
    Set (Fin n → ℝ) :=
  {x | ∃ Y, (x, Y) ∈ MK A b Nprime}

/-- The moment substitution for one variable `k` against a subset `J` of `N'`: `w(J ∪ {k})` if
`k ∈ N'` (idempotent product, `x_k` already in the monomial), `v_J(k)` otherwise (Balas §7.3,
p. 94, Step 2). -/
def MomentEval {n : ℕ} (Nprime : Finset (Fin n)) (w : Finset (Fin n) → ℝ)
    (v : Finset (Fin n) → Fin n → ℝ) (J : Finset (Fin n)) (k : Fin n) : ℝ :=
  if k ∈ Nprime then w (insert k J) else v J k

/-- Row `i`'s linearized Sherali-Adams inequality for the multiplier `∏_{j∈J1} x_j ·
∏_{j∈J2}(1-x_j)`, obtained by expanding the `(1-x_j)` factors via inclusion-exclusion over
subsets `S ⊆ J2` (Balas §7.3, p. 94, Step 1-2). -/
def RowNLt {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (Nprime : Finset (Fin n))
    (w : Finset (Fin n) → ℝ) (v : Finset (Fin n) → Fin n → ℝ) (i : Fin m)
    (J1 J2 : Finset (Fin n)) : ℝ :=
  ∑ S ∈ J2.powerset, (-1 : ℝ) ^ S.card *
    ((∑ k, A i k * MomentEval Nprime w v (J1 ∪ S) k) - b i * w (J1 ∪ S))

/-- `(x,w,v)` represents a point of the lifted Sherali-Adams polyhedron `X_t` at level `t`
(Balas §7.3, p. 94): `w` normalized (`w ∅ = 1`, `w {j} = x_j`), the continuous variables tied to
the lift at the empty monomial (`v_∅(k) = x_k` for `k ∉ N'`, since `v_J(k)` linearizes
`x_k ∏_{j ∈ J} x_j` and `J = ∅` leaves `x_k`), and every level-`t` linearized inequality
nonnegative. Without the tie the continuous coordinates are free of the lift and `K_t` is far
larger than the page's set: for `K = {0 ≤ x₁ ≤ 1, x₂ ≤ 3}`, `N' = {1}`, `t = 1`, the point
`(0.5, 100)` would lie in `K_1` while `conv(K ∩ {x₁ ∈ {0,1}}) ⊆ {x₂ ≤ 3}`. -/
def IsXt {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (Nprime : Finset (Fin n))
    (t : ℕ) (x : Fin n → ℝ) (w : Finset (Fin n) → ℝ) (v : Finset (Fin n) → Fin n → ℝ) : Prop :=
  w ∅ = 1 ∧ (∀ j ∈ Nprime, w {j} = x j) ∧ (∀ k ∉ Nprime, v ∅ k = x k) ∧
    ∀ i (J1 J2 : Finset (Fin n)), Disjoint J1 J2 → J1 ⊆ Nprime → J2 ⊆ Nprime →
      (J1 ∪ J2).card = t → 0 ≤ RowNLt A b Nprime w v i J1 J2

/-- `K_t`, the projection of `X_t` onto the `x`-space (Balas §7.3, p. 94, Step 3). -/
def KtSet {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (Nprime : Finset (Fin n))
    (t : ℕ) : Set (Fin n → ℝ) :=
  {x | ∃ w v, IsXt A b Nprime t x w v}

end Disjunctive.HigherDim
