import Mathlib

namespace ProximalBanach.Hybrid

open Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The (normalized) duality mapping of p. 939:
`J x = {v ∈ E* : ⟨x, v⟩ = ‖x‖² = ‖v‖²}`. The pairing `⟨x, v⟩` is `v x`. -/
def dualityMap (x : E) : Set (StrongDual ℝ E) :=
  {v | v x = ‖x‖ ^ 2 ∧ ‖v‖ ^ 2 = ‖x‖ ^ 2}

variable (E) in
/-- `E` is smooth (p. 939): for all `x, y` on the unit sphere the limit (2.1)
`lim_{t → 0} (‖x + t y‖ - ‖x‖) / t` exists (`t` real, `t ≠ 0`, two-sided). -/
def IsSmooth : Prop :=
  ∀ x y : E, ‖x‖ = 1 → ‖y‖ = 1 →
    ∃ L : ℝ, Tendsto (fun t : ℝ => (‖x + t • y‖ - ‖x‖) / t) (𝓝[≠] (0 : ℝ)) (𝓝 L)

variable (E) in
/-- `E` is uniformly smooth (p. 939): the limit (2.1) is attained uniformly for
`x, y` on the unit sphere, i.e. one `δ` works for all unit `x, y`. -/
def IsUniformlySmooth : Prop :=
  ∃ D : E → E → ℝ, ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
    ∀ x y : E, ‖x‖ = 1 → ‖y‖ = 1 → ∀ t : ℝ, t ≠ 0 → |t| < δ →
      |(‖x + t • y‖ - ‖x‖) / t - D x y| < ε

variable (E) in
/-- `E` is reflexive: the canonical embedding `E → E**` is surjective. -/
def IsReflexive : Prop :=
  Function.Surjective (NormedSpace.inclusionInDoubleDual ℝ E)

/-- A multivalued operator `T : E → 2^{E*}` is monotone (p. 939):
`⟨x₁ - x₂, y₁ - y₂⟩ ≥ 0` whenever `y₁ ∈ T x₁`, `y₂ ∈ T x₂`. -/
def IsMonotoneOp (T : E → Set (StrongDual ℝ E)) : Prop :=
  ∀ x₁ x₂ : E, ∀ y₁ ∈ T x₁, ∀ y₂ ∈ T x₂, 0 ≤ (y₁ - y₂) (x₁ - x₂)

/-- A monotone operator is maximal (p. 939) if its graph is not properly contained in the
graph of any other monotone operator: every monotone `T'` whose graph contains that of `T`
equals `T`. -/
def IsMaximalMonotone (T : E → Set (StrongDual ℝ E)) : Prop :=
  IsMonotoneOp T ∧
    ∀ T' : E → Set (StrongDual ℝ E), IsMonotoneOp T' → (∀ x, T x ⊆ T' x) → T' = T

/-- The zero set `T⁻¹0 = {x ∈ E : 0 ∈ T x}`. -/
def zeros (T : E → Set (StrongDual ℝ E)) : Set E :=
  {x | (0 : StrongDual ℝ E) ∈ T x}

/-- The function `φ(x, y) = ‖x‖² - 2⟨x, J y⟩ + ‖y‖²` of p. 940, for a single-valued
duality map `J`. Note the order: `x` is paired with `J y`. -/
def phi (J : E → StrongDual ℝ E) (x y : E) : ℝ :=
  ‖x‖ ^ 2 - 2 * J y x + ‖y‖ ^ 2

/-- `IsGenProj J C x z` says `z = Q_C x` (p. 940, (2.3)): `z ∈ C` and `z` minimizes
`φ(·, x)` over `C`. -/
def IsGenProj (J : E → StrongDual ℝ E) (C : Set E) (x z : E) : Prop :=
  z ∈ C ∧ ∀ w ∈ C, phi J z x ≤ phi J w x

/-- The half-space `H_n = {z ∈ E : ⟨z - y_n, v_n⟩ ≤ 0}` of (3.1). -/
def halfH (v : ℕ → StrongDual ℝ E) (y : ℕ → E) (n : ℕ) : Set E :=
  {z | v n (z - y n) ≤ 0}

/-- The half-space `W_n = {z ∈ E : ⟨z - x_n, J x_0 - J x_n⟩ ≤ 0}` of (3.1). -/
def halfW (J : E → StrongDual ℝ E) (x : ℕ → E) (n : ℕ) : Set E :=
  {z | (J (x 0) - J (x n)) (z - x n) ≤ 0}

/-- `(x, y, v)` is a run of the algorithm (3.1) (p. 942) with operator `T`, duality map `J`
and parameters `r`, started at `x 0`: for every `n`,
`v_n ∈ T y_n`, `0 = v_n + (1/r_n)(J y_n - J x_n)` and `x_{n+1} = Q_{H_n ∩ W_n} x_0`. -/
def IsHybridRun (T : E → Set (StrongDual ℝ E)) (J : E → StrongDual ℝ E) (r : ℕ → ℝ)
    (x y : ℕ → E) (v : ℕ → StrongDual ℝ E) : Prop :=
  ∀ n : ℕ, v n ∈ T (y n) ∧ v n + (r n)⁻¹ • (J (y n) - J (x n)) = 0 ∧
    IsGenProj J (halfH v y n ∩ halfW J x n) (x 0) (x (n + 1))

end ProximalBanach.Hybrid
