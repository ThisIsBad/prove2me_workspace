import Mathlib

open Filter
open scoped Topology BoundedContinuousFunction

namespace EthierKurtz

open Classical in
/-- Ambient extension used only for differentiation at interior points. -/
noncomputable def closedRegionRestriction {d : ℕ}
    {Ω : Set (EuclideanSpace ℝ (Fin d))}
    (f : (closure Ω) →ᵇ ℝ) (x : EuclideanSpace ℝ (Fin d)) : ℝ :=
  if hx : x ∈ closure Ω then f ⟨x, hx⟩ else 0

end EthierKurtz
