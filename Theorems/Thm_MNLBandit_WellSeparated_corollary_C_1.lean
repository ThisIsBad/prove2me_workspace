import Mathlib
import Definitions.Def_ChoiceCDLP_MNL_mnlObjective
import Definitions.Def_MNLBandit_WellSeparated_Setting

namespace MNLBandit.WellSeparated

open ChoiceCDLP.MNL

/-- Corollary C.1, p. 48, for Algorithm 1 under Assumption 4.1 and `r_i ∈ [0, 1]`, along any
history `h` of `T` customers: the number of epochs `ℓ = 1, …, L` started within the horizon whose
assortment `S_ℓ` contains a product `i` with `T_i(ℓ) < log NT` (`T_i(ℓ)` counting the epochs
`τ ≤ ℓ`, epoch `ℓ` included, that offered `i`) is at most `N log NT`. -/
theorem corollary_C_1 (N : ℕ) (v r : Fin N → ℝ) (𝒮 : Finset (Finset (Fin N)))
    (sel : (Finset (Fin N) → ℝ) → Finset (Fin N))
    (hTU : MNLBandit.UCB.IsTU 𝒮) (hdown : MNLBandit.UCB.DownClosed 𝒮) (hv : ∀ i, 0 ≤ v i ∧ v i ≤ 1)
    (hr : ∀ i, r i ∈ Set.Icc (0 : ℝ) 1) (hsel : MNLBandit.UCB.IsArgmaxSel 𝒮 sel)
    (T : ℕ) (h : Fin T → Option (Fin N)) :
    (((Finset.Icc 1 (epochsStarted r sel h)).filter (fun ℓ =>
        ∃ i ∈ epochSet r sel h ℓ, (Tcount r sel h i ℓ : ℝ) < Real.log (N * T))).card : ℝ)
      ≤ N * Real.log (N * T) := by sorry

end MNLBandit.WellSeparated

