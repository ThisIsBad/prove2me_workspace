import Mathlib
import Definitions.Def_ChoiceCDLP_MNL_mnlObjective
import Definitions.Def_MNLBandit_WellSeparated_Setting

namespace MNLBandit.WellSeparated

open ChoiceCDLP.MNL

/-- Lemma 6.1, p. 20, for Algorithm 1 under Assumption 4.1 and `r_i ∈ [0, 1]`, along any history
`h` of `T` customers: if the UCBs computed at the end of epoch `ℓ` are good, the assortment
`S_{ℓ+1}` chosen from them is offered within the horizon, and every product `i ∈ S_{ℓ+1}` has
`T_i(ℓ) ≥ τ` (and `T_i(ℓ) ≥ 1`), then `S_{ℓ+1}` is optimal: `R(S_{ℓ+1}, v) = R(S*, v)`. -/
theorem lemma_6_1 (N : ℕ) (v r : Fin N → ℝ) (𝒮 : Finset (Finset (Fin N))) (h𝒮 : 𝒮.Nonempty)
    (sel : (Finset (Fin N) → ℝ) → Finset (Fin N))
    (hTU : MNLBandit.UCB.IsTU 𝒮) (hdown : MNLBandit.UCB.DownClosed 𝒮) (hv : ∀ i, 0 ≤ v i ∧ v i ≤ 1)
    (hr : ∀ i, r i ∈ Set.Icc (0 : ℝ) 1) (hsel : MNLBandit.UCB.IsArgmaxSel 𝒮 sel)
    (T : ℕ) (h : Fin T → Option (Fin N)) (ℓ : ℕ)
    (hℓ : ℓ < epochsStarted r sel h) (hgood : IsGood v r sel h ℓ)
    (hcount : ∀ i ∈ epochSet r sel h (ℓ + 1),
      1 ≤ Tcount r sel h i ℓ ∧ tau N T (gap v r 𝒮 h𝒮) ≤ Tcount r sel h i ℓ) :
    revenue v r (epochSet r sel h (ℓ + 1)) = MNLBandit.UCB.optRevenue v r 𝒮 h𝒮 := by sorry

end MNLBandit.WellSeparated

