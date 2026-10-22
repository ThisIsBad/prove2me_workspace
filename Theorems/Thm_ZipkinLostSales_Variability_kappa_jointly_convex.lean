import Mathlib
import Definitions.Def_ZipkinLostSales_Variability_Model
open MeasureTheory

namespace ZipkinLostSales.Variability

/-- Proof of Theorem 11 (Zipkin 2008, p. 941, "the key step"): if the continuation `F` (standing
for `f̄_{t+1}`) is convex and nonnegative on `V`, then `κ̄(v, ζ | d)` of program (4) is jointly
convex in `(v, ζ, d)` on `{v ∈ ZipkinLostSales.LNatural.V, ζ ≤ 0, d ≥ 0}`. -/
theorem kappa_jointly_convex {L : ℕ} (hL : 0 < L) (hh p γ : ℝ) (hhh : 0 ≤ hh) (hp : 0 ≤ p)
    (hγ0 : 0 < γ) (hγ1 : γ ≤ 1) (F : (Fin L → ℝ) → ℝ) (hFconv : ConvexOn ℝ (ZipkinLostSales.LNatural.V L) F)
    (hFnonneg : ∀ v ∈ ZipkinLostSales.LNatural.V L, 0 ≤ F v) :
    ConvexOn ℝ {w : (Fin L → ℝ) × ℝ × ℝ | w.1 ∈ ZipkinLostSales.LNatural.V L ∧ w.2.1 ≤ 0 ∧ 0 ≤ w.2.2}
      (fun w => ZipkinLostSales.LNatural.kappa hh p γ F w.2.2 w.1 w.2.1) := by sorry

end ZipkinLostSales.Variability

