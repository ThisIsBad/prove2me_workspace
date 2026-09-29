import Mathlib

namespace LovaszSchrijver.OddHole

/-- The hyperplane `Hᵢ = {x ∈ ℝ^{n+1} : xᵢ = 0}` (p. 171). -/
def Hplane {ι : Type} (i : ι) : Set (Option ι → ℝ) :=
  {x | x (some i) = 0}

/-- The hyperplane `Gᵢ = {x ∈ ℝ^{n+1} : xᵢ = x₀}` (p. 171). -/
def Gplane {ι : Type} (i : ι) : Set (Option ι → ℝ) :=
  {x | x (some i) = x none}

end LovaszSchrijver.OddHole
