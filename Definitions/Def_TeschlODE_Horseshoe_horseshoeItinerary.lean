import Mathlib
import Definitions.Def_TeschlODE_Horseshoe_horseshoeInv

namespace TeschlODE.Horseshoe

/-- Teschl, §13.1, pp. 332–333, (13.9): the itinerary map `ϕ : Λ → Σ₂ = {0, 1}^ℤ` of the
horseshoe map `F`, `ϕ(x, y)ₙ = yₙ` for `n ≥ 0` and `ϕ(x, y)ₙ = x₋ₙ₋₁` for `n < 0`, where `yₙ` is
defined by `Fⁿ(x, y) ∈ J_{yₙ}` (`J₀ = [0, 1] × [0, 1/µ]`) and `xₙ` by `gⁿ(x, y) ∈ K_{xₙ}`
(`K₀ = [0, λ] × [0, 1]`), `g` the inverse (13.5)–(13.6). Written as "`0` if in `J₀` (resp. `K₀`),
else `1`", which is the book's rule on `Λ`, where every iterate lies in `J₀ ∪ J₁` (resp.
`K₀ ∪ K₁`) and the two strips are disjoint. -/
noncomputable def horseshoeItinerary (lam μ : ℝ) (F : ℝ × ℝ → ℝ × ℝ) (p : ℝ × ℝ) : ℤ → Fin 2 :=
  fun n =>
    if 0 ≤ n then
      (if F^[n.toNat] p ∈ Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) (1 / μ) then 0 else 1)
    else
      (if (horseshoeInv lam μ)^[(-n - 1).toNat] p ∈ Set.Icc (0 : ℝ) lam ×ˢ Set.Icc (0 : ℝ) 1
        then 0 else 1)

end TeschlODE.Horseshoe
