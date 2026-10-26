import Mathlib
import Definitions.Def_ChoiceCDLP_MNL_mnlObjective
import Definitions.Def_MNLBandit_UCB_Setting
import Definitions.Def_MNLBandit_UCB_Algorithm1

namespace MNLBandit.UCB

open ChoiceCDLP.MNL

theorem eq_A_14 {N : ℕ} (v r : Fin N → ℝ)
    (𝒮 : Finset (Finset (Fin N))) (sel : (Finset (Fin N) → ℝ) → Finset (Fin N))
    (hTU : IsTU 𝒮) (hdc : DownClosed 𝒮) (hne : 𝒮.Nonempty) (hsel : IsArgmaxSel 𝒮 sel)
    (hv0 : ∀ i, 0 ≤ v i) (hv1 : ∀ i, v i ≤ 1) (hr : ∀ i, r i ∈ Set.Icc (0 : ℝ) 1)
    (T : ℕ) :
    regret v r 𝒮 hne (alg1 r sel) T ≤
      ∑ h : History N T, histProb v (alg1 r sel) h *
        ∑ ℓ ∈ Finset.range (epochsStarted h),
          (1 + ∑ j ∈ nextSet r sel h ℓ, v j) *
            (optRevenue v r 𝒮 hne - mnlObjective v r 1 (nextSet r sel h ℓ)) := by sorry

end MNLBandit.UCB

