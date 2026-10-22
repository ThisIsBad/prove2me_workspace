import Mathlib
import Definitions.Def_AffinePolicies_Simplex_Setting
import Definitions.Def_AffinePolicies_TwoGap_Setting

namespace AffinePolicies.LargeGap

open Matrix

variable {m n₁ n₂ : ℕ}

/-! ### The instance ℐ of (19), with `n₁ = n₂ = m` -/

/-- `θ₀ = 1 / m^{(1-δ)/2}` (real power). -/
noncomputable def theta0 (m : ℕ) (δ : ℝ) : ℝ := 1 / (m : ℝ) ^ ((1 - δ) / 2)

/-- `r = ⌈m^{1-δ}⌉`. -/
noncomputable def rr (m : ℕ) (δ : ℝ) : ℕ := ⌈(m : ℝ) ^ (1 - δ)⌉₊

/-- `A_ij = 0`. -/
def A19 (m : ℕ) : Matrix (Fin m) (Fin m) ℝ := 0

/-- `B_ij = 1` if `i = j`, `θ₀` otherwise. -/
noncomputable def B19 (m : ℕ) (δ : ℝ) : Matrix (Fin m) (Fin m) ℝ :=
  fun i j => if i = j then 1 else theta0 m δ

/-- `c = 0`. -/
def c19 (m : ℕ) : Fin m → ℝ := 0

/-- `d = (1, …, 1)ᵀ`. -/
def d19 (m : ℕ) : Fin m → ℝ := fun _ => 1

/-- `θ₀ · 1_S`: the vector equal to `θ₀` on the coordinates in `S` and `0` elsewhere.
For `S.card = r` these are `b^{m+2}` (`S` = the first `r` coordinates) and its
permutations `bʲ`, `j ≥ m + 3`. -/
noncomputable def blockPt (m : ℕ) (δ : ℝ) (S : Finset (Fin m)) : Fin m → ℝ :=
  fun i => if i ∈ S then theta0 m δ else 0

/-- `𝒰 = conv{b⁰, b¹, …, b^N}`: the convex hull of `b⁰ = 0`, `bʲ = e_j` (`j = 1, …, m`),
`b^{m+1} = (1/√m)·e`, and the points `θ₀ · 1_S` for every set `S` of exactly `r`
coordinates. -/
noncomputable def U19 (m : ℕ) (δ : ℝ) : Set (Fin m → ℝ) :=
  convexHull ℝ ({0} ∪ Set.range (fun j : Fin m => (Pi.single j (1 : ℝ) : Fin m → ℝ)) ∪
    {fun _ => 1 / Real.sqrt m} ∪
    {b | ∃ S : Finset (Fin m), S.card = rr m δ ∧ b = blockPt m δ S})

/-! ### Permutations: Definition 2 -/

end AffinePolicies.LargeGap
