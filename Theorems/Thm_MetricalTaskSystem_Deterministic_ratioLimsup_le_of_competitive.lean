import Mathlib
import Definitions.Def_MetricalTaskSystem_Deterministic_Model
import Definitions.Def_MetricalTaskSystem_Deterministic_CruelTaskmaster

namespace MetricalTaskSystem.Deterministic

/-- **Lemma 2.1** (Borodin–Linial–Saks 1992, p. 749). If `T` is an infinite (nonnegative) task
sequence whose off-line costs `c₀(T¹ ⋯ Tᵐ)` tend to infinity, then `w_T(A) ≤ w` for every
`w ∈ W_A`; that is, `w(A) = inf W_A ≥ w_T(A)`. -/
theorem ratioLimsup_le_of_competitive {S : Type} [Fintype S] [DecidableEq S] [Nonempty S]
    (d : S → S → ℝ) (hd : IsTaskSystem d) (A : OnlineAlgorithm S) (s₀ : S)
    (T : ℕ → S → ℝ) (hT : ∀ i s, 0 ≤ T i s)
    (hT_inf : Filter.Tendsto (fun m : ℕ => offlineOpt d s₀ (prefixSeq T m))
      Filter.atTop Filter.atTop)
    (w : ℝ) (hw : IsCompetitive d A w) :
    ratioLimsup d A s₀ T ≤ (w : EReal) := by sorry

end MetricalTaskSystem.Deterministic
