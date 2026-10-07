import Mathlib

namespace GoldieRenewal.Implicit

open MeasureTheory Filter Topology
open scoped ENNReal

/-- **The smoothing `f̌`** (Goldie 1991, §1, p. 128):
`f̌(t) := ∫_{−∞}^t e^{−(t−u)} f(u) du`, `t ∈ ℝ`.

**Formalization Note** The integral is a Bochner integral over `(−∞, t]` with respect to Lebesgue
measure. It is the paper's value whenever `u ↦ e^{−(t−u)} f(u)` is integrable on `(−∞, t]`, which
holds for every `t` when `f ∈ L¹(ℝ)` (the kernel is at most `1` there) and for the tail functions
`r` of the mission (they are bounded by `e^{κu}` and the kernel decays). Every statement of the
mission applies it only to such functions. -/
noncomputable def smooth (f : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ u in Set.Iic t, Real.exp (-(t - u)) * f u

/-- The closed cell `[n h, (n+1) h]` of the grid of mesh `h`. -/
def cell (h : ℝ) (n : ℤ) : Set ℝ :=
  Set.Icc ((n : ℝ) * h) (((n : ℝ) + 1) * h)

/-- `sup_{[nh,(n+1)h]} |f|`, computed in `[0, ∞]` (it is `∞` if `f` is unbounded on the cell). -/
noncomputable def cellSupAbs (f : ℝ → ℝ) (h : ℝ) (n : ℤ) : ℝ≥0∞ :=
  ⨆ x ∈ cell h n, ENNReal.ofReal |f x|

/-- The oscillation `sup_{[nh,(n+1)h]} f − inf_{[nh,(n+1)h]} f`, computed in `[0, ∞]` as
`sup_{x, y ∈ cell} (f x − f y)⁺` (it is `∞` if `f` is unbounded on the cell). -/
noncomputable def cellOsc (f : ℝ → ℝ) (h : ℝ) (n : ℤ) : ℝ≥0∞ :=
  ⨆ x ∈ cell h n, ⨆ y ∈ cell h n, ENNReal.ofReal (f x - f y)

/-- **Direct Riemann integrability** (dRi), the notion used in Lemmas 9.1–9.2 of Goldie (1991,
p. 143) and in the key renewal theorem. The paper does not define it; this is the definition of
Feller (1971), *An Introduction to Probability Theory and Its Applications*, Vol. II, §XI.1:
`f : ℝ → ℝ` is directly Riemann-integrable when

1. for every mesh `h > 0` the series `Σ_{n∈ℤ} sup_{[nh,(n+1)h]} |f|` converges (so the upper and
   lower Riemann sums `h Σ_n sup_{[nh,(n+1)h]} f` and `h Σ_n inf_{[nh,(n+1)h]} f` over the whole
   line converge absolutely), and
2. the difference of the upper and lower sums, `h Σ_{n∈ℤ} (sup_{[nh,(n+1)h]} f − inf_{[nh,(n+1)h]} f)`,
   tends to `0` as `h ↓ 0`.

**Formalization Note** Suprema and oscillations are computed in `[0, ∞]`, so an unbounded cell gives
`∞` rather than a junk real value, and condition 1 then fails. Finiteness of the series for one mesh
implies it for every mesh, so "for every `h > 0`" is not a strengthening of Feller's definition. -/
def IsDRi (f : ℝ → ℝ) : Prop :=
  (∀ h : ℝ, 0 < h → ∑' n : ℤ, cellSupAbs f h n < ∞) ∧
    Tendsto (fun h : ℝ => ENNReal.ofReal h * ∑' n : ℤ, cellOsc f h n) (𝓝[>] 0) (𝓝 0)

end GoldieRenewal.Implicit
