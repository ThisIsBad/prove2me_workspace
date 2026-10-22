import Mathlib
open MeasureTheory

namespace OceanicGames.Interior

/-- `w(S) = Σ_{j ∈ S} w_j`, the total weight of a set `S` of major players (§2, p. 2). -/
def wsum {m : ℕ} (w : Fin m → ℝ) (S : Finset (Fin m)) : ℝ := ∑ j ∈ S, w j

/-- `P(t)`: the major players `j` with `x_j < t`, i.e. those placed before the ocean position `t`
(§2, p. 4; strict inequality as printed). -/
noncomputable def pred {m : ℕ} (x : Fin m → ℝ) (t : ℝ) : Finset (Fin m) :=
  Finset.univ.filter (fun j => x j < t)

/-- The unit cube `I^m = [0,1]^m` (Pi order). -/
def cube (m : ℕ) : Set (Fin m → ℝ) := Set.Icc 0 1

/-- `A_i` (§2, p. 5): the points of the cube `I^m` at which major player `i` is pivotal in the
oceanic game `[c; w_1, …, w_m; α]`, i.e. at which the inequalities (2.4)
`w(P(x_i)) + α x_i ≤ c ≤ w(P(x_i)) + w_i + α x_i` hold. -/
def pivotSet {m : ℕ} (c α : ℝ) (w : Fin m → ℝ) (i : Fin m) : Set (Fin m → ℝ) :=
  {x | x ∈ cube m ∧ wsum w (pred x (x i)) + α * x i ≤ c ∧
                    c ≤ wsum w (pred x (x i)) + w i + α * x i}

/-- `φ_i = μ^m(A_i)`, the value of the oceanic game `[c; w_1, …, w_m; α]` to major player `i`
(§2, pp. 4–5): the probability, for `x` uniform on `I^m`, that (2.4) holds. -/
noncomputable def value {m : ℕ} (c α : ℝ) (w : Fin m → ℝ) (i : Fin m) : ℝ :=
  (volume (pivotSet c α w i)).toReal

/-- `Φ`, the combined value of the ocean, defined by (2.5): `Φ + φ(M) = 1`. -/
noncomputable def oceanValue {m : ℕ} (c α : ℝ) (w : Fin m → ℝ) : ℝ :=
  1 - ∑ i, value c α w i

/-- `F(y)` of (4.2), the location in the ordered ocean of the pivot of the game with quota `y`,
for the random point `x ∈ I^m`. The page prints `min {x | w(P(x)) + αx ≥ y}`; the minimum need
not be attained (P is strict), so it is read as the infimum over `t ≥ 0`. -/
noncomputable def pivotLoc {m : ℕ} (α : ℝ) (w : Fin m → ℝ) (x : Fin m → ℝ) (y : ℝ) : ℝ :=
  sInf {t : ℝ | 0 ≤ t ∧ y ≤ wsum w (pred x t) + α * t}

/-- `E{F(y)} = ∫_{I^m} F(y) dx_1 … dx_m` (p. 11). -/
noncomputable def expPivotLoc {m : ℕ} (α : ℝ) (w : Fin m → ℝ) (y : ℝ) : ℝ :=
  ∫ x in cube m, pivotLoc α w x y

/-- The weights `(w_1, …, w_m, w_{m+1})` of the game `Γ⁺` of (4.8): a new major player
`m+1` (index `Fin.last m`) with weight `w'` is appended. -/
def addWeight {m : ℕ} (w : Fin m → ℝ) (w' : ℝ) : Fin (m + 1) → ℝ :=
  Fin.snoc (α := fun _ => ℝ) w w'

/-- The interior condition (5.3): `w(M) ≤ c ≤ α`. -/
def IsInterior {m : ℕ} (c α : ℝ) (w : Fin m → ℝ) : Prop :=
  wsum w Finset.univ ≤ c ∧ c ≤ α

/-- The coefficients `a_n` of (5.6): `a_0 = 1`, `a_n = 1 − n a_{n−1}`. -/
def coeff : ℕ → ℤ
  | 0 => 1
  | n + 1 => 1 - ((n : ℤ) + 1) * coeff n

/-- `π(S)` for `S ⊆ M` (p. 19): the product of `w_j/α` over `j ∈ S` and of `w̄_j/α = (α − w_j)/α`
over `j ∈ M − S`. -/
noncomputable def piProd {m : ℕ} (α : ℝ) (w : Fin m → ℝ) (S : Finset (Fin m)) : ℝ :=
  (∏ j ∈ S, w j / α) * ∏ j ∈ Finset.univ \ S, (α - w j) / α

/-- `π_i(S)` for `S ⊆ M − {i}` (p. 19): the product of `w_j/α` over `j ∈ S` and of
`(α − w_j)/α` over `j ∈ (M − {i}) − S`. -/
noncomputable def piProdErase {m : ℕ} (α : ℝ) (w : Fin m → ℝ) (i : Fin m)
    (S : Finset (Fin m)) : ℝ :=
  (∏ j ∈ S, w j / α) * ∏ j ∈ (Finset.univ.erase i) \ S, (α - w j) / α

end OceanicGames.Interior
