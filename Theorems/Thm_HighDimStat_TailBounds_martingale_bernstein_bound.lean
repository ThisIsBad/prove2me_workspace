import Mathlib
import Definitions.Def_HighDimStat_TailBounds_IsSubExponential

open MeasureTheory

namespace HighDimStat.TailBounds

/-- **Theorem 2.19** (Martingale Bernstein bound), Wainwright, *High-Dimensional Statistics*
(2019), p. 35. Let `{(Dk,Fk)}` be a martingale difference sequence (realized as: `D k` is
`ℱ k`-measurable and `E[D k | ℱ (k-1)] = 0`, for `k = 1,...,n`), and suppose
`E[e^{λDk} | ℱ(k-1)] ≤ e^{λ²νk²/2}` a.s. for `|λ| < 1/αk`. Then (a) `∑Dk` is sub-exponential with
parameters `(√(∑νk²), max αk)`, and (b) `∑Dk` satisfies the two-regime concentration inequality
of Eq. (2.28). Explicit `Integrable` hypotheses on each `D k` and on each conditional-MGF
exponential are required to block Mathlib's `condExp`/Bochner-integral junk value `0` on a
non-integrable argument, which would otherwise let `h_cent`/`h_subexp` hold vacuously for a
non-integrable `D k` (e.g. Cauchy-distributed) regardless of the true martingale-difference or
sub-exponential-MGF property — the same guard `IsSubExponential`'s own definition already uses,
applied here to the conditional form. -/
theorem martingale_bernstein_bound {Ω : Type*} {mΩ : MeasurableSpace Ω} [StandardBorelSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {D : ℕ → Ω → ℝ} {ν α : ℕ → ℝ} {ℱ : Filtration ℕ mΩ}
    (n : ℕ) (hn : 1 ≤ n)
    (h_meas : ∀ k ∈ Finset.Icc 1 n, Measurable[ℱ k] (D k))
    (h_int : ∀ k ∈ Finset.Icc 1 n, Integrable (D k) μ)
    (h_cent : ∀ k ∈ Finset.Icc 1 n, μ[D k | ℱ (k - 1)] =ᵐ[μ] 0)
    (h_subexp_int : ∀ k ∈ Finset.Icc 1 n, ∀ lam : ℝ, (α k = 0 ∨ |lam| < 1 / α k) →
      Integrable (fun ω => Real.exp (lam * D k ω)) μ)
    (h_subexp : ∀ k ∈ Finset.Icc 1 n, ∀ lam : ℝ, (α k = 0 ∨ |lam| < 1 / α k) →
      (μ[fun ω => Real.exp (lam * D k ω) | ℱ (k - 1)]) ≤ᵐ[μ]
        fun _ => Real.exp (lam ^ 2 * (ν k) ^ 2 / 2)) :
    IsSubExponential (fun ω => ∑ k ∈ Finset.Icc 1 n, D k ω) μ
        (Real.sqrt (∑ k ∈ Finset.Icc 1 n, (ν k) ^ 2))
        (Finset.sup' (Finset.Icc 1 n) (Finset.nonempty_Icc.mpr hn) α)
    ∧
    ∀ t : ℝ, 0 ≤ t →
      μ.real {ω | t ≤ |∑ k ∈ Finset.Icc 1 n, D k ω|} ≤
        if t ≤ (∑ k ∈ Finset.Icc 1 n, (ν k) ^ 2) / (Finset.sup' (Finset.Icc 1 n) (Finset.nonempty_Icc.mpr hn) α)
        then 2 * Real.exp (-(t ^ 2) / (2 * ∑ k ∈ Finset.Icc 1 n, (ν k) ^ 2))
        else 2 * Real.exp (-t / (2 * Finset.sup' (Finset.Icc 1 n) (Finset.nonempty_Icc.mpr hn) α)) := by sorry

end HighDimStat.TailBounds
