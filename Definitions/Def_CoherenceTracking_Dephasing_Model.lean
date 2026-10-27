import Mathlib
import Definitions.Def_MIPRE_LCS_Pauli

namespace CoherenceTracking.Dephasing

open Matrix Complex

/-- Qubit operators: `2 × 2` complex matrices, index `0` = `|0⟩`, `1` = `|1⟩`, as in (7). -/
abbrev Qmat := Matrix (Fin 2) (Fin 2) ℂ

/-- Bloch vectors, components in the order `x, y, z`. -/
abbrev BVec := Fin 3 → ℝ

/-- The Pauli matrices `σ_x, σ_y, σ_z`, indexed `0, 1, 2`. -/
def pauli : Fin 3 → Qmat := ![MIPRE.LCS.Pauli.X, MIPRE.LCS.Pauli.Y, MIPRE.LCS.Pauli.Z]

/-- p. 3: a qubit density matrix satisfies `ρ₁₀ = ρ₀₁*` (Hermitian), `Tr ρ = 1`, `Tr ρ² ≤ 1`. -/
def IsQubitState (ρ : Qmat) : Prop :=
  ρᴴ = ρ ∧ ρ.trace = 1 ∧ (ρ * ρ).trace.re ≤ 1

/-- The Bloch vector `v_α = Tr(ρ σ_α)` (the inverse of (9)). -/
noncomputable def blochVec (ρ : Qmat) : BVec := fun α => (ρ * pauli α).trace.re

/-- (9): `ρ = ½ (I + v · σ)`. -/
noncomputable def blochState (v : BVec) : Qmat :=
  (1 / 2 : ℂ) • (1 + ∑ α, ((v α : ℝ) : ℂ) • pauli α)

/-- (11): the coherence `c = v_x² + v_y²`. -/
noncomputable def coherence (ρ : Qmat) : ℝ := blochVec ρ 0 ^ 2 + blochVec ρ 1 ^ 2

/-- (13): `H = (ℏ/2)(ω₀ σ_z + ω₁ σ_x − ω₂ σ_y)`, with `ω 0 = ω₀`, `ω 1 = ω₁`, `ω 2 = ω₂`. -/
noncomputable def hamiltonian (hbar : ℝ) (ω : Fin 3 → ℝ) : Qmat :=
  ((hbar / 2 : ℝ) : ℂ) •
    (((ω 0 : ℝ) : ℂ) • pauli 2 + ((ω 1 : ℝ) : ℂ) • pauli 0 - ((ω 2 : ℝ) : ℂ) • pauli 1)

/-- Right-hand side of (32): `−(i/ℏ)[H, ρ] + (γ/2)(σ_z ρ σ_z − ρ)`. -/
noncomputable def masterRHS (hbar γ : ℝ) (ω : Fin 3 → ℝ) (ρ : Qmat) : Qmat :=
  (-I / (hbar : ℂ)) • (hamiltonian hbar ω * ρ - ρ * hamiltonian hbar ω)
    + ((γ / 2 : ℝ) : ℂ) • (pauli 2 * ρ * pauli 2 - ρ)

/-- The matrix of the Bloch equations (30). -/
def blochMatrix (γ : ℝ) (ω : Fin 3 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![-γ, -ω 0, -ω 2; ω 0, -γ, -ω 1; ω 2, ω 1, 0]

/-- `ρ` solves the master equation (32) on `[0, T)` with controls `ω`: continuous on `[0, T)`,
differentiable with derivative (32) at every `t ∈ (0, T)`. -/
def SolvesMaster (hbar γ : ℝ) (ω : ℝ → Fin 3 → ℝ) (ρ : ℝ → Qmat) (T : ℝ) : Prop :=
  ContinuousOn ρ (Set.Ico 0 T) ∧
    ∀ t ∈ Set.Ioo 0 T, HasDerivAt ρ (masterRHS hbar γ (ω t) (ρ t)) t

/-- `v` solves the Bloch equations (30) on `[0, T)` with controls `ω`. -/
def SolvesBloch (γ : ℝ) (ω : ℝ → Fin 3 → ℝ) (v : ℝ → BVec) (T : ℝ) : Prop :=
  ContinuousOn v (Set.Ico 0 T) ∧
    ∀ t ∈ Set.Ioo 0 T, HasDerivAt v ((blochMatrix γ (ω t)).mulVec (v t)) t

/-- The coherence `v_x² + v_y²` of a Bloch vector. -/
def initCoherence (v0 : BVec) : ℝ := v0 0 ^ 2 + v0 1 ^ 2

/-- (38): the breakdown time `t_b = v_z(0)² / (2 γ c)`. -/
noncomputable def breakdownTime (γ : ℝ) (v0 : BVec) : ℝ :=
  v0 2 ^ 2 / (2 * γ * initCoherence v0)

/-- (37) with `(±) = sign v_z(0)` and `v_x, v_y` frozen at their initial values. -/
noncomputable def trackedBloch (γ : ℝ) (v0 : BVec) (t : ℝ) : BVec :=
  ![v0 0, v0 1, Real.sign (v0 2) * √(v0 2 ^ 2 - 2 * γ * initCoherence v0 * t)]

/-- (41)–(42) with `(±) = sign v_z(0)`; component `0` is the free field `ω₀`,
component `1` is `ω₁` (42), component `2` is `ω₂` (41). -/
noncomputable def trackingFields (γ : ℝ) (v0 : BVec) (ω0 : ℝ → ℝ) (t : ℝ) : Fin 3 → ℝ :=
  ![ω0 t,
    Real.sign (v0 2) * (-γ * v0 1 + ω0 t * v0 0) / √(v0 2 ^ 2 - 2 * γ * initCoherence v0 * t),
    Real.sign (v0 2) * (-γ * v0 0 - ω0 t * v0 1) / √(v0 2 ^ 2 - 2 * γ * initCoherence v0 * t)]

/-- The tracked density matrix `½ (I + v(t) · σ)` with `v(t)` from (37). -/
noncomputable def trackedState (γ : ℝ) (v0 : BVec) (t : ℝ) : Qmat :=
  blochState (trackedBloch γ v0 t)

end CoherenceTracking.Dephasing
