import Mathlib

open Filter Topology Set

namespace PorteusSS

/-! The concave increasing ordering cost of §II. Throughout, `c : ℝ → ℝ` is the ordering cost
function (only its values on `[0, ∞)` matter) and `κ` denotes a slope in the set `C` of the
paper, which the paper also writes `c`. -/

/-- `C₁(z) = {(κ, K) ∈ ℝ² ; κ z + K = c(z) and κ y + K ≥ c(y) for all y ≥ 0}`: the lines
supporting `c` on `[0, ∞)` and touching it at `z`. -/
def C1 (c : ℝ → ℝ) (z : ℝ) : Set (ℝ × ℝ) :=
  {p | p.1 * z + p.2 = c z ∧ ∀ y : ℝ, 0 ≤ y → c y ≤ p.1 * y + p.2}

/-- `C₂(z) = {(κ, K) ∈ C₁(z) ; K ≤ K' for all (κ', K') ∈ C₁(z)}`. -/
def C2 (c : ℝ → ℝ) (z : ℝ) : Set (ℝ × ℝ) :=
  {p | p ∈ C1 c z ∧ ∀ q ∈ C1 c z, p.2 ≤ q.2}

/-- `C = {κ ∈ ℝ ; (κ, K) ∈ C₂(z) for some K ≥ 0 and z > 0}`. -/
def slopeSet (c : ℝ → ℝ) : Set ℝ :=
  {κ | ∃ K : ℝ, 0 ≤ K ∧ ∃ z : ℝ, 0 < z ∧ (κ, K) ∈ C2 c z}

/-- `K_κ` for `κ ∈ C`: the real number with `(κ, K_κ) ∈ C₂(x)` for some `x > 0`. The set below is
a singleton for `κ ∈ C` (two supporting lines of the same slope that touch `c` coincide), so the
infimum is that number. Only used for `κ ∈ slopeSet c`. -/
noncomputable def Kc (c : ℝ → ℝ) (κ : ℝ) : ℝ :=
  sInf {K : ℝ | ∃ z : ℝ, 0 < z ∧ (κ, K) ∈ C2 c z}

/-- The standing assumptions of §II on the ordering cost: `c` is concave and increasing
(nondecreasing) on `[0, ∞)`, `c 0 = 0`, and `lim_{z ↓ 0} C₂(z) = (c₀, K₀)`,
`lim_{z → ∞} C₂(z) = (c_∞, K_∞)` exist (every element of `C₂(z)` is eventually in any
neighbourhood of the limit pair). -/
structure IsOrderingCost (c : ℝ → ℝ) (c0 K0 cInf KInf : ℝ) : Prop where
  concave : ConcaveOn ℝ (Ici 0) c
  mono : MonotoneOn c (Ici 0)
  zero : c 0 = 0
  lim_zero : ∀ U ∈ 𝓝 ((c0, K0) : ℝ × ℝ), ∀ᶠ z in 𝓝[>] (0 : ℝ), C2 c z ⊆ U
  lim_top : ∀ U ∈ 𝓝 ((cInf, KInf) : ℝ × ℝ), ∀ᶠ z in atTop, C2 c z ⊆ U

end PorteusSS
