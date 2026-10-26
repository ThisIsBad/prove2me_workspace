import Mathlib
import Definitions.Def_ChoiceCDLP_MNL_mnlObjective
import Definitions.Def_MNLBandit_WellSeparated_Setting

namespace MNLBandit.WellSeparated

open ChoiceCDLP.MNL

open Classical in
/-- Lemma 6.2, p. 20, for Algorithm 1 under Assumption 4.1 and `r_i ∈ [0, 1]`, along any history
`h` of `T` customers: among the epochs started within the horizon, at most `Nτ` are good epochs
offering a sub-optimal assortment (epoch `ℓ + 1` counted when the UCBs computed at the end of
epoch `ℓ` are good and `R(S_{ℓ+1}, v) < R(S*, v)`). -/
theorem lemma_6_2 (N : ℕ) (v r : Fin N → ℝ) (𝒮 : Finset (Finset (Fin N))) (h𝒮 : 𝒮.Nonempty)
    (sel : (Finset (Fin N) → ℝ) → Finset (Fin N))
    (hTU : MNLBandit.UCB.IsTU 𝒮) (hdown : MNLBandit.UCB.DownClosed 𝒮) (hv : ∀ i, 0 ≤ v i ∧ v i ≤ 1)
    (hr : ∀ i, r i ∈ Set.Icc (0 : ℝ) 1) (hsel : MNLBandit.UCB.IsArgmaxSel 𝒮 sel)
    (T : ℕ) (h : Fin T → Option (Fin N)) :
    (((Finset.range (epochsStarted r sel h)).filter (fun ℓ =>
        IsGood v r sel h ℓ ∧
          revenue v r (epochSet r sel h (ℓ + 1)) < MNLBandit.UCB.optRevenue v r 𝒮 h𝒮)).card : ℝ)
      ≤ N * tau N T (gap v r 𝒮 h𝒮) := by sorry

end MNLBandit.WellSeparated

