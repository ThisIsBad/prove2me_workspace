import Mathlib
import Definitions.Def_QueueingFundamentals_Networks_ClosedJackson

namespace QueueingFundamentals.Networks

/-- Eqs. (4.14)–(4.16), pp.196: for a closed Jackson network of `k ≥ 1` single-server nodes with
service rates `μ_i > 0`, an irreducible routing matrix `R` and any positive solution `ρ` of the
traffic equations (4.16), a distribution `p` on the `N`-customer states is a steady-state solution
of the balance equations (4.14) if and only if it is the product form (4.15) normalized by
`G(N) = ∑_{n_1+⋯+n_k=N} ρ_1^{n_1} ⋯ ρ_k^{n_k}`. -/
theorem closed_product_form {k : ℕ} [NeZero k] (mu : Fin k → ℝ) (R : Fin k → Fin k → ℝ)
    (rho : Fin k → ℝ) (hmu : ∀ i, 0 < mu i) (hR : IsRoutingMatrix R) (hirr : IsIrreducible R)
    (hrho : ∀ i, 0 < rho i) (htraffic : IsTrafficSolution mu R rho) (N : ℕ)
    (p : (Fin k → ℕ) → ℝ) :
    IsClosedSteadyState mu R N p ↔ p = productForm (fun i n => rho i ^ n) N := by sorry

end QueueingFundamentals.Networks

