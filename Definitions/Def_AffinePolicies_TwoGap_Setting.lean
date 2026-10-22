import Mathlib
import Definitions.Def_AffinePolicies_Simplex_Setting

namespace AffinePolicies.TwoGap

open Matrix

variable {m n₁ n₂ : ℕ}

/-! ### The instance ℐ of (6), with `n₁ = n₂ = m` -/

/-- `A_ij = 0`. -/
def A6 (m : ℕ) : Matrix (Fin m) (Fin m) ℝ := 0

/-- `B_ij = 1` if `i = j`, `1/√m` otherwise. -/
noncomputable def B6 (m : ℕ) : Matrix (Fin m) (Fin m) ℝ :=
  fun i j => if i = j then 1 else 1 / Real.sqrt m

/-- `c = 0`. -/
def c6 (m : ℕ) : Fin m → ℝ := 0

/-- `d = (1, …, 1)ᵀ`. -/
def d6 (m : ℕ) : Fin m → ℝ := fun _ => 1

/-- `b^{m+1}`: `1/√m` on the first `m/2` coordinates (0-based indices `0, …, m/2 - 1`),
`0` on the rest. -/
noncomputable def bLow (m : ℕ) : Fin m → ℝ :=
  fun i => if (i : ℕ) < m / 2 then 1 / Real.sqrt m else 0

/-- `b^{m+2}`: `0` on the first `m/2` coordinates, `1/√m` on the last `m/2`. -/
noncomputable def bHigh (m : ℕ) : Fin m → ℝ :=
  fun i => if m / 2 ≤ (i : ℕ) then 1 / Real.sqrt m else 0

/-- `𝒰 = conv{b⁰, b¹, …, b^{m+2}}` with `b⁰ = 0`, `bʲ = e_j` (`j = 1, …, m`),
`b^{m+1} = bLow m`, `b^{m+2} = bHigh m`. -/
noncomputable def U6 (m : ℕ) : Set (Fin m → ℝ) :=
  convexHull ℝ ({0} ∪ Set.range (fun j : Fin m => (Pi.single j (1 : ℝ) : Fin m → ℝ)) ∪
    {bLow m, bHigh m})

/-! ### Permutations: Definition 2 and the set Γ of (10) -/

/-- Definition 2: `U` is permutation-invariant with respect to `τ` iff
`x ∈ U ↔ x^τ ∈ U` for all `x`, where `x^τ = (x_{τ(1)}, …, x_{τ(m)}) = x ∘ τ`. -/
def IsPermInvariant (U : Set (Fin m → ℝ)) (τ : Equiv.Perm (Fin m)) : Prop :=
  ∀ x : Fin m → ℝ, x ∈ U ↔ x ∘ τ ∈ U

/-- (10): `Γ = {τ ∈ S^m | i ≤ m/2 ↔ τ(i) ≤ m/2}`; with 0-based indices the paper's
`i ≤ m/2` reads `(i : ℕ) < m / 2`. -/
def Gamma (m : ℕ) : Set (Equiv.Perm (Fin m)) :=
  {τ | ∀ i : Fin m, (i : ℕ) < m / 2 ↔ ((τ i : Fin m) : ℕ) < m / 2}

end AffinePolicies.TwoGap
