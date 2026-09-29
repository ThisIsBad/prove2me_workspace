import Mathlib
import Definitions.Def_MetricalTaskSystem_Deterministic_Model
import Definitions.Def_MetricalTaskSystem_Deterministic_ContinuousTime
import Definitions.Def_MetricalTaskSystem_Deterministic_AstarD

namespace MetricalTaskSystem.Deterministic

/-- **Lemma 6.2** (Borodin–Linial–Saks 1992, p. 756). Let `t_k` be the time at which `A*_d`
enters `s_k` on the (nonnegative) task sequence `T¹ ⋯ Tᵐ` (`t₀ = 1`), and let
`h_k(x) = φ_{t_k}(x)` be the optimal off-line (continuous-time) cost up to time `t_k` subject
to being in state `x` at time `t_k`. Then `h_k(x) ≥ f_k(x)` for all states `x`. -/
theorem astar_f_le_offline {S : Type} [Fintype S] [DecidableEq S] [Nontrivial S]
    (d : S → S → ℝ) (hd : IsTaskSystem d) (s₀ : S) (s : ℕ → S) (hs : IsAstarSeq d s₀ s)
    (m : ℕ) (T : Fin m → S → ℝ) (hT : ∀ i x, 0 ≤ T i x)
    (k : ℕ) (tk : ℝ) (htk : entryTime s (cSeq d s) T k = some tk) (x : S) :
    fSeq d s k x ≤ offlineCostTo d s₀ T tk x := by sorry

end MetricalTaskSystem.Deterministic

