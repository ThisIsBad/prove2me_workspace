import Mathlib
import Definitions.Def_ThreeOpSplitting_Convergence_MonotoneOperators
import Definitions.Def_DouglasRachfordPPA_GenDR_Operators
import Definitions.Def_DouglasRachfordPPA_GenDR_SplittingOperator
import Definitions.Def_ThreeOpSplitting_Convergence_WeakConvergence

open InnerProductSpace ThreeOpSplitting.Convergence

namespace DouglasRachfordPPA.GenDR
/-- Theorem 7 (generalized Douglas–Rachford splitting): for `lam > 0`, maximal monotone `A`, `B`
with resolvent maps `JA = J_{lam A}`, `JB = J_{lam B}`, sequences satisfying (T1)–(T3) with
summable nonnegative errors `α`, `β` and relaxation factors `0 < inf ρ ≤ sup ρ < 2`:
if `zer(A + B) ≠ ∅` then `z` converges weakly to a point of `Z*_lam`; if `zer(A + B) = ∅`
then `z` is unbounded. `v 0` is unused (the paper indexes `v` from `1`). -/
theorem generalized_douglas_rachford_convergence {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (A B : H → Set H) (hA : IsMaximalMonotone A) (hB : IsMaximalMonotone B)
    (lam : ℝ) (hlam : 0 < lam)
    (JA JB : H → H) (hJA : IsResolvent lam A JA) (hJB : IsResolvent lam B JB)
    (z u v : ℕ → H) (α β ρ : ℕ → ℝ)
    (hT1 : ∀ k, ‖u k - JB (z k)‖ ≤ β k)
    (hT2 : ∀ k, ‖v (k + 1) - JA ((2 : ℝ) • u k - z k)‖ ≤ α k)
    (hT3 : ∀ k, z (k + 1) = z k + ρ k • (v (k + 1) - u k))
    (hα_nonneg : ∀ k, 0 ≤ α k) (hβ_nonneg : ∀ k, 0 ≤ β k)
    (hα_sum : Summable α) (hβ_sum : Summable β)
    (hρ : ∃ ρ₁ ρ₂ : ℝ, 0 < ρ₁ ∧ ρ₂ < 2 ∧ ∀ k, ρ₁ ≤ ρ k ∧ ρ k ≤ ρ₂) :
    ((zer (opAdd A B)).Nonempty → ∃ zs ∈ Zstar lam A B, WeakTendsto z zs) ∧
    (zer (opAdd A B) = ∅ → ¬ Bornology.IsBounded (Set.range z)) := by sorry

end DouglasRachfordPPA.GenDR

