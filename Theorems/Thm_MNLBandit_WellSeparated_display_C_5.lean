import Mathlib
import Definitions.Def_ChoiceCDLP_MNL_mnlObjective
import Definitions.Def_MNLBandit_WellSeparated_Setting

namespace MNLBandit.WellSeparated

open ChoiceCDLP.MNL

/-- Display (C.5), p. 48 (the epoch rewriting of the regret, as an inequality), for Algorithm 1
under Assumption 4.1 and `r_i ∈ [0, 1]`:
`Reg_π(T, v) ≤ 𝔼_π ∑_{ℓ=1}^{L} (1 + V(S_ℓ))(R(S*, v) − R(S_ℓ, v))`, `V(S) = ∑_{j∈S} v_j`, where `L`
is the number of epochs started within the first `T` customers. -/
theorem display_C_5 (N : ℕ) (v r : Fin N → ℝ) (𝒮 : Finset (Finset (Fin N))) (h𝒮 : 𝒮.Nonempty)
    (sel : (Finset (Fin N) → ℝ) → Finset (Fin N))
    (hTU : MNLBandit.UCB.IsTU 𝒮) (hdown : MNLBandit.UCB.DownClosed 𝒮) (hv : ∀ i, 0 ≤ v i ∧ v i ≤ 1)
    (hr : ∀ i, r i ∈ Set.Icc (0 : ℝ) 1) (hsel : MNLBandit.UCB.IsArgmaxSel 𝒮 sel) (T : ℕ) :
    MNLBandit.UCB.regret v r 𝒮 h𝒮 (alg1 r sel) T ≤
      ∑ h : Fin T → Option (Fin N), histProb v (alg1 r sel) T h *
        ∑ ℓ ∈ Finset.Icc 1 (epochsStarted r sel h),
          (1 + ∑ j ∈ epochSet r sel h ℓ, v j) *
            (MNLBandit.UCB.optRevenue v r 𝒮 h𝒮 - revenue v r (epochSet r sel h ℓ)) := by sorry

end MNLBandit.WellSeparated

