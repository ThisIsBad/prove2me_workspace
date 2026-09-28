import Mathlib
import Definitions.Def_BealeConvexMin_SumLargest_sumLargest
import Definitions.Def_BealeConvexMin_SumLargest_Forms

namespace BealeConvexMin.SumLargest

/-- Beale (1955), proof of Theorem 1 (a), p. 180, the display after "Then". If
`u'_1 ≤ u'_2 ≤ ⋯ ≤ u'_s` and `u'_τ ≤ 0` (so at least `τ` of `L_1, …, L_s` are not less than
`L_0`), then

`C = A_0 + τ c_00 + Σ_l (A_l + τ c_0l) z'_l + Σ_{f=1}^{τ} (φ_f + τθ_f − 1) u'_f
      + Σ_{f=τ+1}^{s} (φ_f + τθ_f) u'_f`
`  = A_0 + τ c_00 + Σ_l (A_l + τ c_0l) z'_l + Σ_{f=1}^{τ} (φ_f + τθ_f − 1)(u'_f − u'_τ)
      + Σ_{f=τ+1}^{s} (φ_f + τθ_f)(u'_f − u'_τ) + {Σ_{f=1}^{s} (φ_f + τθ_f) − τ} u'_τ`.

Index shift: the paper's `f = 1, …, s` is Lean's `f = 0, …, s-1`, so the paper's `f ≤ τ` is
`(f : ℕ) < τ`, `f > τ` is `τ ≤ (f : ℕ)`, and `u'_τ` is `u' ⟨τ - 1, _⟩`. The page's second line
prints `c_l` for `c_0l` (a misprint); `c_0l` is used here. -/
theorem rearrangement {r s : ℕ} (P : Forms r s) (τ : ℕ) (hτ1 : 1 ≤ τ) (hτs : τ ≤ s)
    (z' : Fin r → ℝ) (u' : Fin s → ℝ) (hmono : Monotone u')
    (hτneg : u' ⟨τ - 1, by omega⟩ ≤ 0) :
    P.C τ z' u' =
        P.A0 + (τ : ℝ) * P.c00 + ∑ l, (P.A l + (τ : ℝ) * P.c0 l) * z' l
          + ∑ f ∈ Finset.univ.filter (fun f : Fin s => (f : ℕ) < τ),
              (P.φ f + (τ : ℝ) * P.θ f - 1) * u' f
          + ∑ f ∈ Finset.univ.filter (fun f : Fin s => τ ≤ (f : ℕ)),
              (P.φ f + (τ : ℝ) * P.θ f) * u' f ∧
    P.C τ z' u' =
        P.A0 + (τ : ℝ) * P.c00 + ∑ l, (P.A l + (τ : ℝ) * P.c0 l) * z' l
          + ∑ f ∈ Finset.univ.filter (fun f : Fin s => (f : ℕ) < τ),
              (P.φ f + (τ : ℝ) * P.θ f - 1) * (u' f - u' ⟨τ - 1, by omega⟩)
          + ∑ f ∈ Finset.univ.filter (fun f : Fin s => τ ≤ (f : ℕ)),
              (P.φ f + (τ : ℝ) * P.θ f) * (u' f - u' ⟨τ - 1, by omega⟩)
          + (∑ f, (P.φ f + (τ : ℝ) * P.θ f) - (τ : ℝ)) * u' ⟨τ - 1, by omega⟩ := by sorry

end BealeConvexMin.SumLargest

