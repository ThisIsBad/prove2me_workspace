import Mathlib

namespace FirstOrderOpt.OperatorSliding

/-- Corollary 8.1(a) (gradient sliding complexity, explicit constant, `N` fixed a priori). `Ψ :=
f+h+chi` on the closed convex `X` (8.1.1), `x*` an optimal solution. `{p_t},{θ_t}` are set to
(8.1.39): `p_t = t/2`, which (via (8.1.44), cited not restated) gives the closed form `P_t =
2/((t+1)(t+2))` for every `t` (including `t=0`, matching `P_0=1`) and (via (8.1.46)) `Γ_k =
2/(k(k+1))` for `k≥1`. `{β_k},{γ_k},{T_k}` are set to (8.1.40): `β_k = 2L/k`, `γ_k = 2/(k+1)`,
`T_k = ⌈M²Nk²/(DtildeL²)⌉` for a designer-chosen `Dtilde>0` (a free parameter of the algorithm's schedule,
not derived from `X` or `f`). `hBd` is `gs_convergence_bound` (Theorem 8.1(a), this mission's other
milestone) applied with this schedule: `Ψ(xbar N)-Ψ(x*) ≤ Bd(N)`, the general (8.1.34) bound,
carried as a hypothesis rather than re-derived here. The goal is the algebraic simplification
(8.1.45)-(8.1.48) of `Bd(N)` under this schedule into the closed form (8.1.41).

**Formalization Note.** The book's own printed `βk = 2L/(νk)` (8.1.40) is an OCR/typesetting
artifact of the source text extraction; the proof's own line "`γkβk/(Γk(1−PTk)) = 2L/(1−PTk)`"
(p. 494/PDF 504, using `Γk=2/(k(k+1))` and `γk=2/(k+1)`) is consistent only with `βk = 2L/k`,
which is what is formalized here.

**Formalization Note (revised 2026-09-19).** `hM` tightened from `0 ≤ M` to `0 < M` per (8.1.3)'s
own "for some `L>0` and `M>0`". Load-bearing here (not merely cosmetic): together with `N ≥ 1`,
`Dtilde > 0`, `L > 0`, this makes `T k = ⌈M²Nk²/(Dtilde·L²)⌉₊` the ceiling of a strictly positive
real for every `k ≥ 1`, hence `T k ≥ 1` automatically — closing the same junk-value division
corner as `gs_convergence_bound`'s `hTpos` fix without needing a separate hypothesis here. -/
theorem explicit_gs_rate {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (X : Set E) (f h chi Ψ : E → ℝ) (hΨ : ∀ u, Ψ u = f u + h u + chi u)
    (V : E → E → ℝ) (hVnonneg : ∀ a b, 0 ≤ V a b)
    (L M : ℝ) (hL : 0 < L) (hM : 0 < M)
    (x0 xstar : E) (hx0 : x0 ∈ X) (hxstar : xstar ∈ X)
    (hxstarOpt : ∀ w ∈ X, Ψ xstar ≤ Ψ w)
    (N : ℕ) (hN : 1 ≤ N) (Dtilde : ℝ) (hDtilde : 0 < Dtilde)
    (p P Γ β γ : ℕ → ℝ) (T : ℕ → ℕ)
    (hp : ∀ t : ℕ, p t = (t : ℝ) / 2)
    (hP : ∀ t : ℕ, P t = 2 / (((t : ℝ) + 1) * ((t : ℝ) + 2)))
    (hΓ : ∀ k : ℕ, 1 ≤ k → Γ k = 2 / ((k : ℝ) * ((k : ℝ) + 1)))
    (hβ : ∀ k : ℕ, 1 ≤ k → β k = 2 * L / (k : ℝ))
    (hγ : ∀ k : ℕ, 1 ≤ k → γ k = 2 / ((k : ℝ) + 1))
    (hT : ∀ k : ℕ, 1 ≤ k → T k = ⌈M ^ 2 * (N : ℝ) * (k : ℝ) ^ 2 / (Dtilde * L ^ 2)⌉₊)
    (xbar : ℕ → E) (hxbar0 : xbar 0 = x0)
    (hBd : Ψ (xbar N) - Ψ xstar ≤
      Γ N * β 1 / (1 - P (T 1)) * V x0 xstar
        + M ^ 2 * Γ N / 2 *
            ∑ k ∈ Finset.Icc 1 N, ∑ i ∈ Finset.Icc 1 (T k),
              γ k * P (T k) / (Γ k * β k * (1 - P (T k)) * p i ^ 2 * P (i - 1))) :
    Ψ (xbar N) - Ψ xstar ≤ 2 * L / ((N : ℝ) * ((N : ℝ) + 1)) * (3 * V x0 xstar + 2 * Dtilde) := by sorry

end FirstOrderOpt.OperatorSliding
