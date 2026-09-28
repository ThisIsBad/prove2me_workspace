import Mathlib
import Definitions.Def_LassoDantzig_REConditions_RE

namespace LassoDantzig.REConditions

/-- The quadratic form `xᵀ Ψ_n x = (1/n) |X x|_2²` of the Gram matrix `Ψ_n = XᵀX/n` (p. 5). -/
noncomputable def gramQuad {n M : ℕ} (X : Matrix (Fin n) (Fin M) ℝ) (x : Fin M → ℝ) : ℝ :=
  (1 / (n : ℝ)) * ∑ i, (X.mulVec x i) ^ 2

/-- The set of Rayleigh quotients `xᵀΨ_n x / |x|_2²` over `x ∈ ℝ^M` with `1 ≤ 𝓜(x) ≤ u`. -/
def rayleighSet {n M : ℕ} (X : Matrix (Fin n) (Fin M) ℝ) (u : ℕ) : Set ℝ :=
  {q | ∃ x : Fin M → ℝ, 1 ≤ sparsity x ∧ sparsity x ≤ u ∧
    q = gramQuad X x / ∑ j, x j ^ 2}

/-- The restricted eigenvalue `φ_min(u) = min_{1 ≤ 𝓜(x) ≤ u} xᵀΨ_n x / |x|_2²` (p. 8).
For `1 ≤ u` and `M ≥ 1` the set is nonempty (a basis vector) and lies in a bounded interval
`[0, C]`, and the minimum is attained, so `sInf` is the paper's minimum. -/
noncomputable def phiMin {n M : ℕ} (X : Matrix (Fin n) (Fin M) ℝ) (u : ℕ) : ℝ :=
  sInf (rayleighSet X u)

/-- The restricted eigenvalue `φ_max(u) = max_{1 ≤ 𝓜(x) ≤ u} xᵀΨ_n x / |x|_2²` (p. 8).
For `1 ≤ u` and `M ≥ 1` the set is nonempty and bounded, and the maximum is attained, so
`sSup` is the paper's maximum. -/
noncomputable def phiMax {n M : ℕ} (X : Matrix (Fin n) (Fin M) ℝ) (u : ℕ) : ℝ :=
  sSup (rayleighSet X u)

/-- The set whose maximum is the restricted correlation `θ_{m1,m2}` (p. 8): the values
`c1ᵀ X_{I1}ᵀ X_{I2} c2 / (n |c1|_2 |c2|_2)` over disjoint `I1, I2` with `|I1| ≤ m1`,
`|I2| ≤ m2` and non-zero `c1 ∈ ℝ^{I1}`, `c2 ∈ ℝ^{I2}` (encoded as vectors of `ℝ^M` supported in
`I1`, `I2`, so that `c1ᵀ X_{I1}ᵀ X_{I2} c2 = ∑_i (X c1)_i (X c2)_i`). -/
def corrSet {n M : ℕ} (X : Matrix (Fin n) (Fin M) ℝ) (m1 m2 : ℕ) : Set ℝ :=
  {t | ∃ I1 I2 : Finset (Fin M), Disjoint I1 I2 ∧ I1.card ≤ m1 ∧ I2.card ≤ m2 ∧
    ∃ c1 c2 : Fin M → ℝ, (∀ j, j ∉ I1 → c1 j = 0) ∧ (∀ j, j ∉ I2 → c2 j = 0) ∧
      c1 ≠ 0 ∧ c2 ≠ 0 ∧
      t = (∑ i, X.mulVec c1 i * X.mulVec c2 i) /
        ((n : ℝ) * Real.sqrt (∑ j, c1 j ^ 2) * Real.sqrt (∑ j, c2 j ^ 2))}

/-- The restricted correlation `θ_{m1,m2}` (p. 8). For `M ≥ 2`, `m1, m2 ≥ 1` the set is
nonempty (two disjoint singletons), bounded (Cauchy–Schwarz) and its maximum is attained, so
`sSup` is the paper's maximum; the set is symmetric under `c1 ↦ -c1`, so `θ ≥ 0`. -/
noncomputable def theta {n M : ℕ} (X : Matrix (Fin n) (Fin M) ℝ) (m1 m2 : ℕ) : ℝ :=
  sSup (corrSet X m1 m2)

/-- Assumption 1 (p. 8): `φ_min(2s) > c₀ θ_{s,2s}`. (The ranges `1 ≤ s ≤ M/2`, `c₀ > 0` are
hypotheses of the theorems that use it.) -/
def Assumption1 {n M : ℕ} (X : Matrix (Fin n) (Fin M) ℝ) (s : ℕ) (c0 : ℝ) : Prop :=
  c0 * theta X s (2 * s) < phiMin X (2 * s)

/-- Assumption 2 (pp. 8–9): `m φ_min(s + m) > c₀² s φ_max(m)`. (The ranges `1 ≤ s ≤ M/2`,
`m ≥ s`, `s + m ≤ M`, `c₀ > 0` are hypotheses of the theorems that use it.) -/
def Assumption2 {n M : ℕ} (X : Matrix (Fin n) (Fin M) ℝ) (s m : ℕ) (c0 : ℝ) : Prop :=
  c0 ^ 2 * (s : ℝ) * phiMax X m < (m : ℝ) * phiMin X (s + m)

/-- `κ₁(s, c₀) = √φ_min(2s) · (1 − c₀ θ_{s,2s} / φ_min(2s))` (p. 9). -/
noncomputable def kappa1 {n M : ℕ} (X : Matrix (Fin n) (Fin M) ℝ) (s : ℕ) (c0 : ℝ) : ℝ :=
  Real.sqrt (phiMin X (2 * s)) * (1 - c0 * theta X s (2 * s) / phiMin X (2 * s))

/-- `κ₂(s, m, c₀) = √φ_min(s+m) · (1 − c₀ √(s φ_max(m) / (m φ_min(s+m))))` (p. 9). -/
noncomputable def kappa2 {n M : ℕ} (X : Matrix (Fin n) (Fin M) ℝ) (s m : ℕ) (c0 : ℝ) : ℝ :=
  Real.sqrt (phiMin X (s + m)) *
    (1 - c0 * Real.sqrt ((s : ℝ) * phiMax X m / ((m : ℝ) * phiMin X (s + m))))

end LassoDantzig.REConditions
