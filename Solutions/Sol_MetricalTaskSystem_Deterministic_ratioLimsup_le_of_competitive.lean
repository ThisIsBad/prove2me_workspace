import Mathlib
import Definitions.Def_MetricalTaskSystem_Deterministic_Model
import Definitions.Def_MetricalTaskSystem_Deterministic_CruelTaskmaster

namespace MetricalTaskSystem.Deterministic
end MetricalTaskSystem.Deterministic

open MetricalTaskSystem.Deterministic

theorem solution {S : Type} [Fintype S] [DecidableEq S] [Nonempty S]
    (d : S → S → ℝ) (hd : IsTaskSystem d) (A : OnlineAlgorithm S) (s₀ : S)
    (T : ℕ → S → ℝ) (hT : ∀ i s, 0 ≤ T i s)
    (hT_inf : Filter.Tendsto (fun m : ℕ => offlineOpt d s₀ (prefixSeq T m))
      Filter.atTop Filter.atTop)
    (w : ℝ) (hw : IsCompetitive d A w) :
    ratioLimsup d A s₀ T ≤ (w : EReal) := by
  obtain ⟨_hwpos, K, hK⟩ := hw
  set C : ℝ := max K 0 with hC
  let g : ℕ → ℝ := fun m => w + C / offlineOpt d s₀ (prefixSeq T m)
  have hg : Filter.Tendsto g Filter.atTop (nhds w) := by
    have h0 : Filter.Tendsto (fun m : ℕ => C / offlineOpt d s₀ (prefixSeq T m))
        Filter.atTop (nhds 0) := tendsto_const_nhds.div_atTop hT_inf
    simpa [g] using (tendsto_const_nhds (x := w)).add h0
  have hgE : Filter.Tendsto (fun m => ((g m : ℝ) : EReal)) Filter.atTop (nhds (w : EReal)) :=
    EReal.tendsto_coe.mpr hg
  have hev : ∀ᶠ m in Filter.atTop,
      (((onlineCost d A s₀ (prefixSeq T m) / offlineOpt d s₀ (prefixSeq T m) : ℝ)) : EReal)
        ≤ ((g m : ℝ) : EReal) := by
    filter_upwards [hT_inf.eventually_gt_atTop 0] with m hm
    rw [EReal.coe_le_coe_iff]
    have h1 := hK s₀ m (prefixSeq T m) (fun i s => hT i s)
    have h2 : onlineCost d A s₀ (prefixSeq T m) ≤ w * offlineOpt d s₀ (prefixSeq T m) + C :=
      h1.trans (by simp [hC])
    show _ ≤ w + C / offlineOpt d s₀ (prefixSeq T m)
    rw [div_le_iff₀ hm, add_mul, div_mul_cancel₀ _ hm.ne']
    linarith
  unfold ratioLimsup
  calc Filter.limsup _ Filter.atTop
      ≤ Filter.limsup (fun m => ((g m : ℝ) : EReal)) Filter.atTop :=
        Filter.limsup_le_limsup hev
    _ = (w : EReal) := hgE.limsup_eq
