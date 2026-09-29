import Mathlib
import Definitions.Def_LewisTorczon_BoundPS_Box
import Definitions.Def_LewisTorczon_BoundPS_ProjQ
import Definitions.Def_LewisTorczon_BoundPS_GPS

namespace LewisTorczon.BoundPS

/-- **Theorem 2.2** (Theorem 3.2 of Torczon 1997), p. 5, eq. (5), with `r_LB`, `r_UB` as identified
on p. 10: write `τ = β/α` with `α, β ∈ ℕ` coprime, and `Δ_k = τ^{r_k} Δ_0` with `r_k ∈ ℤ`. For
every `N ≥ 1` there are integer vectors `z_0, …, z_{N-1}` with
`x_N = x_0 + (β^{r_LB} α^{-r_UB}) Δ_0 B Σ_{k=0}^{N-1} z_k`, where
`r_LB = min_{0 ≤ k < N} r_k` and `r_UB = max_{0 ≤ k < N} r_k`. -/
theorem theorem_2_2 {n m : ℕ} (P : GPSParams n) (lo hi : Fin n → EReal)
    (hlohi : ∀ j, lo j < hi j) (f : EuclideanSpace ℝ (Fin n) → ℝ) (R : GPSRun n m)
    (hR : IsGPSRun P lo hi f R) (α β : ℕ) (hα : 0 < α) (hcop : Nat.Coprime α β)
    (hτ : P.τ = (β : ℚ) / (α : ℚ)) (r : ℕ → ℤ)
    (hr : ∀ k, R.Δ k = (P.τ : ℝ) ^ r k * R.Δ 0) (N : ℕ) (hN : 1 ≤ N) :
    ∃ z : ℕ → (Fin n → ℤ),
      R.x N = R.x 0 +
        ((β : ℝ) ^ ((Finset.range N).inf' (Finset.nonempty_range_iff.mpr (by omega)) r) *
            (α : ℝ) ^ (-((Finset.range N).sup' (Finset.nonempty_range_iff.mpr (by omega)) r)) *
            R.Δ 0) •
          WithLp.toLp 2 (P.B.mulVec (fun i => (((∑ k ∈ Finset.range N, z k i : ℤ)) : ℝ))) := by sorry

end LewisTorczon.BoundPS
