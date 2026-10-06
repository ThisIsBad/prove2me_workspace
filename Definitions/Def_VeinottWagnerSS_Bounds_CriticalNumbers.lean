import Mathlib

namespace VeinottWagnerSS.Bounds

/-- `S̲` ("S underbar", `\underline{S}`), p. 537: the smallest integer that minimizes `G_α`.
Defined as the infimum of the set of global minimizers of `G`; when `G` is convex and
`G(y) → ∞` as `|y| → ∞` that set is nonempty and bounded below, so this is its least element.
(On a set that is empty or unbounded below, `sInf` on `ℤ` returns `0`; every theorem using
`SLow` assumes `G` coercive.) -/
noncomputable def SLow (G : ℤ → ℝ) : ℤ :=
  sInf {y : ℤ | ∀ z : ℤ, G y ≤ G z}

/-- `S̄` ("S bar", `\bar{S}`), Eq. (21), p. 537: the smallest integer `S̄ ≥ S̲` for which
`G_α(S̄ + 1) ≥ G_α(S̲) + αK`. -/
noncomputable def SHigh (G : ℤ → ℝ) (K α : ℝ) : ℤ :=
  sInf {y : ℤ | SLow G ≤ y ∧ G (SLow G) + α * K ≤ G (y + 1)}

/-- `s̲` ("s underbar", `\underline{s}`), Eq. (22), p. 537: the smallest integer for which
`G_α(s̲) ≤ G_α(S̲) + K`. -/
noncomputable def sLow (G : ℤ → ℝ) (K : ℝ) : ℤ :=
  sInf {y : ℤ | G y ≤ G (SLow G) + K}

/-- `s̄` ("s bar", `\bar{s}`), Eq. (23), p. 537: the smallest integer for which
`G_α(s̄) ≤ G_α(S̲) + (1 − α)K`. -/
noncomputable def sHigh (G : ℤ → ℝ) (K α : ℝ) : ℤ :=
  sInf {y : ℤ | G y ≤ G (SLow G) + (1 - α) * K}

end VeinottWagnerSS.Bounds
