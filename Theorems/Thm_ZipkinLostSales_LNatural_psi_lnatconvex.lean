import Mathlib
import Definitions.Def_ZipkinLostSales_LNatural_Model
open MeasureTheory

namespace ZipkinLostSales.LNatural

/-- Proof of Theorem 4 (Zipkin 2008, p. 939): if the continuation `F` (standing for `f̄_{t+1}`) is
L♮-convex on `V`, the objective `ψ_t(v₊, v, ζ)` of (4) is L♮-convex on its constraint set
(coordinates `(v₊, v₀, …, v_{L−1}, ζ)`). -/
theorem psi_lnatconvex (L : ℕ) (hL : 0 < L) (hh p γ : ℝ) (hhh : 0 ≤ hh) (hp : 0 ≤ p)
    (hγ0 : 0 < γ) (hγ1 : γ ≤ 1) (F : (Fin L → ℝ) → ℝ) (hF : LNatConvexOn (V L) F)
    (d : ℝ) (hd : 0 ≤ d) :
    LNatConvexOn (Dpsi L d) (liftPsi hh p γ F d) := by sorry

end ZipkinLostSales.LNatural

