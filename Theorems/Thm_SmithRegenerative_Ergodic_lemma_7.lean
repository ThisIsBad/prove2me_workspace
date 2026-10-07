import Mathlib

open MeasureTheory ProbabilityTheory Filter Topology

namespace SmithRegenerative.Ergodic

/-- **Lemma 7** (Smith, *Regenerative stochastic processes*, Proc. R. Soc. Lond. A
232(1188):6–31 (1955), §5·3, p. 26): "If {x_n} (n = 1, 2, …), is a sequence of independent,
identically distributed random variables for which E|x_n|^p < ∞, (p > 0), then
lim_{n→∞} x_n/n^{1/p} = 0 with probability one."

Formalization Note: the paper's `x_1, x_2, …` are `x 1, x 2, …`; `x 0` is unconstrained and does
not affect the limit. Independence is mutual independence of `(x (n+1))_{n ≥ 0}`, identical
distribution is `IdentDistrib (x (n+1)) (x 1)`, and `E|x_n|^p < ∞` is integrability of
`|x_1|^p` (real power). `n^{1/p}` is `Real.rpow`; at `n = 0` it is `0` and the quotient is `0`,
which does not affect the limit. -/
theorem lemma_7 {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (x : ℕ → Ω → ℝ) (p : ℝ) (hp : 0 < p)
    (hindep : iIndepFun (fun n : ℕ => x (n + 1)) P)
    (hident : ∀ n, IdentDistrib (x (n + 1)) (x 1) P P)
    (hmom : Integrable (fun ω => |x 1 ω| ^ p) P) :
    ∀ᵐ ω ∂P, Tendsto (fun n : ℕ => x n ω / (n : ℝ) ^ (1 / p)) atTop (𝓝 0) := by sorry

end SmithRegenerative.Ergodic

