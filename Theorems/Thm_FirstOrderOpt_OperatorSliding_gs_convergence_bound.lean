import Mathlib

namespace FirstOrderOpt.OperatorSliding

/-- Theorem 8.1(a) (general convergence of the outer gradient-sliding, GS, algorithm, unbounded-`X`
case). `Ψ := f+h+chi` on the closed convex `X` (8.1.1). The GS algorithm (Algorithm 8.1) keeps an
"outer" iterate `xIter k` and running average `xbar k` (`xbar 0 = x0`, `xIter 0 = x0`), calling the
PS procedure at each outer step; `hRecursion` is (8.1.26), Proposition 8.2's per-outer-step
recursion (cited, not restated: it is itself proved by combining `ps_procedure_bound`, this
mission's Proposition 8.1, with the model-function inequalities (8.1.27)-(8.1.31)). `P` is (8.1.20)
(cited, not restated) and `Γ` is (8.1.32). `hβγ` is (8.1.25) and `hMono` is (8.1.33), the
unbounded-`X` monotonicity condition part (a) needs. Conclusion: for any `N≥1`, `Ψ(xbar N)-Ψ(x*) ≤
Bd(N)` as in (8.1.34), a sum over outer steps `k=1,…,N` of a further sum over the PS procedure's
own inner steps `i=1,…,T k` called at outer step `k`.

**Formalization Note (revised 2026-09-19).** `hM` tightened to `0 < M` per (8.1.3)'s own "for some
`L>0` and `M>0`". `hTpos` (`T k ≥ 1`) added: without it, `T k = 0` gives `P (T k) = P 0 = 1` (via
`hP0`), so `1 - P (T k) = 0` and `(1 - P (T k))⁻¹ = 0` by Lean's real-division junk convention,
silently zeroing the corresponding term of `hRecursion` and the conclusion at `k=1` — a
zero-length PS call the book's Algorithm 8.1 (p. 488/PDF 498) never contemplates. -/
theorem gs_convergence_bound {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (X : Set E) (f h chi Ψ : E → ℝ) (hΨ : ∀ u, Ψ u = f u + h u + chi u)
    (V : E → E → ℝ) (hVnonneg : ∀ a b, 0 ≤ V a b)
    (L M : ℝ) (hL : 0 < L) (hM : 0 < M)
    (x0 xstar : E) (hx0 : x0 ∈ X) (hxstar : xstar ∈ X)
    (hxstarOpt : ∀ w ∈ X, Ψ xstar ≤ Ψ w)
    (p θ P : ℕ → ℝ) (hp : ∀ t, 0 < p t) (hP0 : P 0 = 1)
    (hPrec : ∀ t : ℕ, 1 ≤ t → P t = p t * (1 + p t)⁻¹ * P (t - 1))
    (hθ : ∀ t : ℕ, 1 ≤ t → θ t = (P (t - 1) - P t) / ((1 - P t) * P (t - 1)))
    (β γ : ℕ → ℝ) (T : ℕ → ℕ) (hTpos : ∀ k : ℕ, 1 ≤ k → 1 ≤ T k)
    (hγ1 : γ 1 = 1) (hβγ : ∀ k : ℕ, 1 ≤ k → 0 ≤ β k - L * γ k)
    (Γ : ℕ → ℝ) (hΓ1 : Γ 1 = 1) (hΓrec : ∀ k : ℕ, 2 ≤ k → Γ k = (1 - γ k) * Γ (k - 1))
    (hMono : ∀ k : ℕ, 2 ≤ k →
      γ k * β k / (Γ k * (1 - P (T k))) ≤ γ (k - 1) * β (k - 1) / (Γ (k - 1) * (1 - P (T (k - 1)))))
    (xIter xbar : ℕ → E) (hxIter0 : xIter 0 = x0) (hxbar0 : xbar 0 = x0)
    (hRecursion : ∀ w ∈ X, ∀ k : ℕ, 1 ≤ k →
      Ψ (xbar k) - Ψ w ≤ (1 - γ k) * (Ψ (xbar (k - 1)) - Ψ w)
        + γ k * (1 - P (T k))⁻¹ *
          (β k * V (xIter (k - 1)) w - β k * V (xIter k) w
            + M ^ 2 * P (T k) / (2 * β k) * ∑ i ∈ Finset.Icc 1 (T k), (p i ^ 2 * P (i - 1))⁻¹))
    (N : ℕ) (hN : 1 ≤ N) :
    Ψ (xbar N) - Ψ xstar ≤
      Γ N * β 1 / (1 - P (T 1)) * V x0 xstar
        + M ^ 2 * Γ N / 2 *
            ∑ k ∈ Finset.Icc 1 N, ∑ i ∈ Finset.Icc 1 (T k),
              γ k * P (T k) / (Γ k * β k * (1 - P (T k)) * p i ^ 2 * P (i - 1)) := by sorry

end FirstOrderOpt.OperatorSliding
