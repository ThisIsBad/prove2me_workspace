import Mathlib
import Definitions.Def_PhiDivRobust_Counterpart_IsPhiDivergenceFunction
import Definitions.Def_PhiDivRobust_Counterpart_uncertaintySet
import Definitions.Def_PhiDivRobust_Counterpart_perspConj
open Matrix

namespace PhiDivRobust.Counterpart

/-- Theorem 1 of Ben-Tal et al. 2013 (p. 347), stated for `q > 0` (the printed `q ≥ 0` is false):
`x` satisfies `(a + Bp)ᵀx ≤ β` for all `p` in the φ-divergence region (12), where `q ∈ U`, iff there
are `η ∈ ℝᵏ`, `λ ∈ ℝ` with `η ≥ 0`, `λ ≥ 0` and
`aᵀx + dᵀη + ρλ + ∑ᵢ qᵢ · λφ*((bᵢᵀx − cᵢᵀη)/λ) ≤ β` (13), with `0φ*(s/0) := 0` for `s ≤ 0` and
`+∞` for `s > 0`; `bᵢ`, `cᵢ` are the `i`-th columns of `B` and `C`. -/
theorem robust_counterpart_iff {n m k : ℕ} (φ : ℝ → EReal) (hφ : IsPhiDivergenceFunction φ)
    (a : Fin n → ℝ) (B : Matrix (Fin n) (Fin m) ℝ) (β : ℝ) (C : Matrix (Fin k) (Fin m) ℝ)
    (d : Fin k → ℝ) (q : Fin m → ℝ) (ρ : ℝ) (hq : ∀ i, 0 < q i) (hρ : 0 < ρ)
    (hqU : q ∈ uncertaintySet φ C d q ρ) (x : Fin n → ℝ) :
    (∀ p ∈ uncertaintySet φ C d q ρ, (a + B *ᵥ p) ⬝ᵥ x ≤ β) ↔
      ∃ η : Fin k → ℝ, ∃ lam : ℝ, 0 ≤ η ∧ 0 ≤ lam ∧
        ((a ⬝ᵥ x + d ⬝ᵥ η + ρ * lam : ℝ) : EReal) +
          ∑ i, (q i : EReal) *
            perspConj φ lam ((fun j => B j i) ⬝ᵥ x - (fun j => C j i) ⬝ᵥ η) ≤ (β : EReal) := by sorry

end PhiDivRobust.Counterpart

