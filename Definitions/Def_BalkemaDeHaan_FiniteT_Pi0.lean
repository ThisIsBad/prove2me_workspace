import Mathlib

namespace BalkemaDeHaan.FiniteT

/-- The limit distribution functions `Π_{0,c}` of Balkema–de Haan (1974), for every real `c`.
For `c > 0` (p. 793): `Π_{0,c}(x) = Γ_{c⁻¹}(c x) = 1 - (1 + c x)^{-1/c}` for `x ≥ 0`;
for `c = 0` (p. 793): `Π_{0,0}(x) = Π(x) = 1 - e^{-x}` for `x ≥ 0`;
for `c < 0` (p. 801): `Π_{0,c}(x) = 1 - (1 + c x)^{-1/c}` for `0 ≤ x ≤ |c|⁻¹`, and (completion,
not printed) `Π_{0,c}(x) = 1` for `x > |c|⁻¹`.
All of them vanish for `x < 0` (p. 793). -/
noncomputable def pi0 (c x : ℝ) : ℝ :=
  if x < 0 then 0
  else if c = 0 then 1 - Real.exp (-x)
  else if 0 < c then 1 - (1 + c * x) ^ (-1 / c)
  else if x ≤ |c|⁻¹ then 1 - (1 + c * x) ^ (-1 / c)
  else 1

/-- The auxiliary function of the proof of Lemma 4 (p. 803):
`σ(u) = ∫₀¹ ∫₀ᵗ e^{-u s} ds dt`, which equals `u⁻²(e^{-u} - 1 + u)` for `u ≠ 0`. -/
noncomputable def sigma (u : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..1, ∫ s in (0 : ℝ)..t, Real.exp (-(u * s))

end BalkemaDeHaan.FiniteT
