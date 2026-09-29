import Mathlib

open scoped OnePoint
open Filter Set

namespace MilnorDynamics

/-- Affine coordinate of the Riemann sphere near finite points: `z ↦ z`, with the junk value
`∞ ↦ 0` (only ever used near points where the value is finite). -/
def chartFinite : OnePoint ℂ → ℂ
  | some z => z
  | none => 0

/-- Coordinate of the Riemann sphere near `∞`: `z ↦ z⁻¹`, `∞ ↦ 0` (so `0 ↦ 0` is a junk value;
it is only ever used near points where the value is different from `0`). -/
noncomputable def chartInfinite : OnePoint ℂ → ℂ
  | some z => z⁻¹
  | none => 0

/-- The chordal (spherical) metric on the Riemann sphere `ℂ ∪ {∞}`: the Euclidean distance
between the images on the unit sphere of `ℝ³` under inverse stereographic projection. -/
noncomputable def chordalDist : OnePoint ℂ → OnePoint ℂ → ℝ
  | some z, some w => 2 * ‖z - w‖ / (Real.sqrt (1 + ‖z‖ ^ 2) * Real.sqrt (1 + ‖w‖ ^ 2))
  | some z, none => 2 / Real.sqrt (1 + ‖z‖ ^ 2)
  | none, some w => 2 / Real.sqrt (1 + ‖w‖ ^ 2)
  | none, none => 0

/-- `f : ℂ → ℂ ∪ {∞}` is a holomorphic map from the open set `U` to the Riemann sphere:
it is continuous on `U`, and in the two standard coordinate charts of the sphere
(`z` near finite values, `1/z` near values different from `0`) it is complex differentiable. -/
def IsHolomorphicOn (U : Set ℂ) (f : ℂ → OnePoint ℂ) : Prop :=
  ContinuousOn f U ∧
  (∀ z ∈ U, f z ≠ ∞ → DifferentiableAt ℂ (fun w => chartFinite (f w)) z) ∧
  (∀ z ∈ U, f z ≠ ((0 : ℂ) : OnePoint ℂ) → DifferentiableAt ℂ (fun w => chartInfinite (f w)) z)

/-- Locally uniform convergence on `U` of maps into the Riemann sphere, with respect to the
chordal metric: uniform convergence on every compact subset of `U`. -/
def TendstoLocallyUniformlyOnSphere (F : ℕ → ℂ → OnePoint ℂ) (g : ℂ → OnePoint ℂ)
    (U : Set ℂ) : Prop :=
  ∀ K ⊆ U, IsCompact K → ∀ ε > 0, ∀ᶠ n in atTop, ∀ x ∈ K, chordalDist (F n x) (g x) < ε

/-- A family `𝓕` of maps from `U` to the (compact) Riemann sphere is *normal* on `U` if every
sequence in `𝓕` has a subsequence converging locally uniformly on `U` (chordal metric) to some
continuous map `g : U → ℂ ∪ {∞}`. -/
def IsNormalFamily (U : Set ℂ) (𝓕 : Set (ℂ → OnePoint ℂ)) : Prop :=
  ∀ f : ℕ → ℂ → OnePoint ℂ, (∀ n, f n ∈ 𝓕) →
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ g : ℂ → OnePoint ℂ,
      ContinuousOn g U ∧ TendstoLocallyUniformlyOnSphere (fun n => f (φ n)) g U

/-- A sequence of maps `f n : U → V` *diverges locally uniformly from `V`* if for all compact
`K ⊆ U` and `K' ⊆ V` we have `f n (K) ∩ K' = ∅` for all sufficiently large `n`. -/
def DivergesLocallyUniformlyFrom (f : ℕ → ℂ → ℂ) (U V : Set ℂ) : Prop :=
  ∀ K ⊆ U, IsCompact K → ∀ K' ⊆ V, IsCompact K' → ∀ᶠ n in atTop, ∀ x ∈ K, f n x ∉ K'

/-- A family `𝓕` of maps from `U` into the (possibly noncompact) set `V ⊆ ℂ` is *normal* if
every sequence in `𝓕` has either a subsequence converging locally uniformly on `U` to a
continuous map `g : U → V`, or a subsequence diverging locally uniformly from `V`. -/
def IsNormalFamilyInto (U V : Set ℂ) (𝓕 : Set (ℂ → ℂ)) : Prop :=
  ∀ f : ℕ → ℂ → ℂ, (∀ n, f n ∈ 𝓕) →
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ((∃ g : ℂ → ℂ, ContinuousOn g U ∧ MapsTo g U V ∧
          TendstoLocallyUniformlyOn (fun n => f (φ n)) g atTop U) ∨
        DivergesLocallyUniformlyFrom (fun n => f (φ n)) U V)

end MilnorDynamics
