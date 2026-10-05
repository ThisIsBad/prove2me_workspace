import Mathlib
import Definitions.Def_SennottDP_ContinuousTime_ApproxSeq
import Definitions.Def_SennottDP_ContinuousTime_CTMDC

open scoped ENNReal
open Filter Topology
open MeasureTheory ProbabilityTheory

namespace SennottDP.ContinuousTime

lemma cexd_exp_mean {r : ℝ} (hr : 0 < r) :
    ∫⁻ s, ENNReal.ofReal s ∂(expMeasure r) = ENNReal.ofReal (1 / r) := by
  unfold expMeasure gammaMeasure
  have hm : Measurable (gammaPDF 1 r) := (measurable_gammaPDFReal 1 r).ennreal_ofReal
  have hid : Measurable (fun s : ℝ => ENNReal.ofReal s) := measurable_id.ennreal_ofReal
  rw [lintegral_withDensity_eq_lintegral_mul _ hm hid]
  have h1 : ∀ x, (gammaPDF 1 r * fun s => ENNReal.ofReal s) x =
      (Set.Ioi (0:ℝ)).indicator (fun x => ENNReal.ofReal (r * (x ^ ((2:ℝ) - 1) * Real.exp (-(r * x))))) x := by
    intro x
    simp only [Pi.mul_apply]
    by_cases hx : 0 < x
    · rw [Set.indicator_of_mem (Set.mem_Ioi.mpr hx)]
      have : gammaPDF 1 r x = exponentialPDF r x := rfl
      rw [this, exponentialPDF_of_nonneg hx.le, ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      norm_num; ring
    · rw [Set.indicator_of_notMem (by simpa using hx)]
      rw [ENNReal.ofReal_of_nonpos (by linarith), mul_zero]
  simp_rw [h1]
  rw [lintegral_indicator measurableSet_Ioi]
  have hint : ∫ x in Set.Ioi (0:ℝ), r * (x ^ ((2:ℝ) - 1) * Real.exp (-(r * x))) = 1 / r := by
    rw [integral_const_mul, Real.integral_rpow_mul_exp_neg_mul_Ioi (by norm_num) hr]
    rw [show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast]
    norm_num [Real.Gamma_two]
    field_simp
  rw [integral_eq_lintegral_of_nonneg_ae] at hint
  · have hne : (∫⁻ x in Set.Ioi (0:ℝ), ENNReal.ofReal (r * (x ^ ((2:ℝ) - 1) * Real.exp (-(r * x))))) ≠ ⊤ := by
      intro h; rw [h] at hint; simp at hint; exact absurd hint (by positivity)
    rw [← hint, ENNReal.ofReal_toReal hne]
  · rw [EventuallyLE, ae_restrict_iff' measurableSet_Ioi]
    exact ae_of_all _ (fun x (hx : 0 < x) ↦ by positivity)
  · exact (by fun_prop : Measurable fun x : ℝ => r * (x ^ ((2:ℝ) - 1) * Real.exp (-(r * x)))).aestronglyMeasurable


def cexPartner (i : ℕ) : ℕ := if i % 2 = 0 then i + 1 else i - 1

lemma cexPartner_ne (i : ℕ) : cexPartner i ≠ i := by unfold cexPartner; split_ifs <;> omega
lemma cexPartner_small {i : ℕ} (h : i ≤ 1) : cexPartner i ≤ 1 := by unfold cexPartner; split_ifs <;> omega
lemma cexPartner_big {i : ℕ} (h : 2 ≤ i) : 2 ≤ cexPartner i := by unfold cexPartner; split_ifs <;> omega
lemma cexPartner_le {i : ℕ} : cexPartner i ≤ i + 1 := by unfold cexPartner; split_ifs <;> omega

noncomputable def cexΨ : CTMDC ℕ Unit where
  A _ := {()}
  G _ _ := 0
  g i _ := if i ≤ 1 then 1 else 0
  ν _ _ := 1
  P i _ j := if j = cexPartner i then 1 else 0

lemma cex_valid : cexΨ.IsValid := by
  refine ⟨fun i => by simp [cexΨ], fun i a _ => ?_, fun i a _ => ?_, fun i a _ => ?_⟩
  · simp only [cexΨ]; refine ⟨le_rfl, by split_ifs <;> norm_num, by norm_num⟩
  · simp [cexΨ]
  · simp [cexΨ, (cexPartner_ne i).symm]

lemma cex_CTB : cexΨ.CTB (1/2) 1 := by
  refine ⟨by norm_num, ⟨1/2, by norm_num, fun i a _ => ?_⟩, fun i a _ => ?_⟩ <;>
    simp [CTMDC.meanSojourn, cexΨ] <;> norm_num

/-- Under any policy, the expected time of `n` periods is `n`. -/
lemma cex_time (θ : cexΨ.Policy) :
    ∀ n k sa t i, CTMDC.expectedSum θ (fun _ _ s => ENNReal.ofReal s) n k sa t i = n := by
  intro n; induction n with
  | zero => intros; simp [CTMDC.expectedSum]
  | succ n ih =>
    intro k sa t i
    simp only [CTMDC.expectedSum, ih]
    have hA : cexΨ.A i = {()} := rfl
    have hσ := θ.σ_sum k sa t i
    rw [hA, Finset.sum_singleton] at hσ ⊢
    rw [hσ, one_mul]
    have hν : cexΨ.ν i () = 1 := rfl
    have hP : (fun j => cexΨ.P i () j * (n : ℝ≥0∞)) = fun j => if j = cexPartner i then (n : ℝ≥0∞) else 0 := by
      funext j; simp only [cexΨ]; split_ifs <;> simp
    rw [hP, tsum_ite_eq, hν]
    have := isProbabilityMeasure_expMeasure (r := 1) one_pos
    rw [lintegral_add_right _ measurable_const, lintegral_const, measure_univ, mul_one,
      cexd_exp_mean one_pos]
    push_cast; simp [add_comm]

lemma cex_cost_ge (θ : cexΨ.Policy) :
    ∀ n k sa t i, i ≤ 1 → CTMDC.expectedSum θ (fun _ _ s => ENNReal.ofReal s) n k sa t i ≤
      CTMDC.expectedSum θ cexΨ.periodCost n k sa t i := by
  intro n; induction n with
  | zero => intros; simp [CTMDC.expectedSum]
  | succ n ih =>
    intro k sa t i hi
    simp only [CTMDC.expectedSum]
    refine Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_left (lintegral_mono fun s =>
      add_le_add ?_ (ENNReal.tsum_le_tsum fun j => ?_)) (by positivity)
    · simp [CTMDC.periodCost, cexΨ, hi]
    · by_cases hj : j = cexPartner i
      · exact mul_le_mul_of_nonneg_left (ih _ _ _ _ (hj ▸ cexPartner_small hi)) (by positivity)
      · simp [cexΨ, hj]

lemma cex_avgValue_ge (i : ℕ) (hi : i ≤ 1) : 1 ≤ cexΨ.avgValue i := by
  refine le_iInf fun θ => ?_
  unfold CTMDC.avgCost
  apply le_limsup_of_frequently_le'
  apply Eventually.frequently
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hT : CTMDC.expTimeN θ n i = n := cex_time θ n 0 _ _ i
  have hC : (n : ℝ≥0∞) ≤ CTMDC.expCostN θ n i := by
    rw [← hT]; exact cex_cost_ge θ n 0 _ _ i hi
  rw [hT]
  have hn0 : (n : ℝ≥0∞) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  rw [ENNReal.le_div_iff_mul_le (Or.inl hn0) (Or.inl (ENNReal.natCast_ne_top n)), one_mul]
  exact hC

noncomputable abbrev cexΔ : MDC ℕ Unit := cexΨ.aux (1/2)

lemma cexΔ_P (i j : ℕ) : cexΔ.P i () j =
    if j = i then ENNReal.ofReal (1/2) else if j = cexPartner i then ENNReal.ofReal (1/2) else 0 := by
  simp only [cexΔ, CTMDC.aux, cexΨ]
  split_ifs <;> norm_num

lemma cexΔ_Psum (i : ℕ) : ∑' j, cexΔ.P i () j = 1 := by
  have hf : (fun j => cexΔ.P i () j) = fun j => (if j = i then ENNReal.ofReal (1/2) else 0) +
      (if j = cexPartner i then ENNReal.ofReal (1/2) else 0) := by
    funext j; rw [cexΔ_P]
    have := cexPartner_ne i
    split_ifs <;> first | omega | simp
  rw [hf, ENNReal.tsum_add, tsum_ite_eq, tsum_ite_eq, ← ENNReal.ofReal_add (by norm_num) (by norm_num)]
  norm_num

lemma cexΔ_σ (θ : cexΔ.Policy) (h : List (ℕ × Unit)) (i : ℕ) : θ.σ h i () = 1 := by
  have := θ.σ_sum h i
  have hA : cexΔ.A i = {()} := rfl
  rwa [hA, Finset.sum_singleton] at this

lemma cex_mass (θ : cexΔ.Policy) (i : ℕ) :
    ∀ t, ∑' h, ∑' j, MDC.histProb θ i t h j ≤ 1 := by
  intro t; induction t with
  | zero =>
    rw [tsum_eq_single []]
    · simp only [MDC.histProb]; rw [tsum_eq_single i (fun j hj => by simp [hj])]; simp
    · intro h hh
      cases h with
      | nil => exact absurd rfl hh
      | cons x h => simp [MDC.histProb]
  | succ t ih =>
    have hinj : Function.Injective (fun p : (ℕ × Unit) × List (ℕ × Unit) => p.1 :: p.2) := by
      intro p q hpq; simp only [List.cons.injEq] at hpq; exact Prod.ext hpq.1 hpq.2
    rw [← hinj.tsum_eq]
    · have : ∀ p : (ℕ × Unit) × List (ℕ × Unit),
          ∑' j, MDC.histProb θ i (t + 1) (p.1 :: p.2) j = MDC.histProb θ i t p.2 p.1.1 := by
        rintro ⟨⟨k, u⟩, h⟩
        simp only [MDC.histProb]
        rw [ENNReal.tsum_mul_left, cexΔ_Psum, cexΔ_σ, mul_one, mul_one]
      simp_rw [this]
      have hp := ENNReal.tsum_prod (f := fun (x : ℕ × Unit) (h : List (ℕ × Unit)) =>
        MDC.histProb θ i t h x.1)
      try simp only at hp
      rw [hp, ENNReal.tsum_comm]
      calc ∑' h, ∑' (x : ℕ × Unit), MDC.histProb θ i t h x.1
          = ∑' h, ∑' j, MDC.histProb θ i t h j := by
            congr 1; funext h
            have hq := ENNReal.tsum_prod (f := fun (j : ℕ) (_ : Unit) => MDC.histProb θ i t h j)
            try simp only at hq
            rw [hq]
            simp
        _ ≤ 1 := ih
    · intro h hh
      cases h with
      | nil => exact absurd (by simp [MDC.histProb]) hh
      | cons x h => exact ⟨(x, h), rfl⟩

lemma cex_zero (θ : cexΔ.Policy) (i : ℕ) (hi : 2 ≤ i) :
    ∀ t h j, j ≤ 1 → MDC.histProb θ i t h j = 0 := by
  intro t; induction t with
  | zero =>
    intro h j hj
    cases h with
    | nil => simp [MDC.histProb]; omega
    | cons x h => simp [MDC.histProb]
  | succ t ih =>
    intro h j hj
    cases h with
    | nil => simp [MDC.histProb]
    | cons x h =>
      obtain ⟨k, u⟩ := x
      simp only [MDC.histProb]
      by_cases hk : k ≤ 1
      · rw [ih h k hk]; simp
      · rw [cexΔ_P]
        have := cexPartner_big (show 2 ≤ k by omega)
        rw [if_neg (by omega), if_neg (by omega), mul_zero]

noncomputable def cexθ : cexΔ.Policy := cexΔ.ofStationary (fun _ => ()) (fun i => by simp [cexΔ, CTMDC.aux, cexΨ])

lemma cexΔ_avgValue_le (i : ℕ) : cexΔ.avgValue i ≤ 1 := by
  refine le_trans (iInf_le _ cexθ) ?_
  unfold MDC.avgCost
  apply limsup_le_of_le (by isBoundedDefault)
  apply Eventually.of_forall
  intro n
  apply ENNReal.div_le_of_le_mul
  rw [one_mul]
  calc ∑ t ∈ Finset.range n, MDC.expectedCost cexθ i t ≤ ∑ t ∈ Finset.range n, (1 : ℝ≥0∞) := by
        apply Finset.sum_le_sum; intro t _
        unfold MDC.expectedCost
        refine le_trans ?_ (cex_mass cexθ i t)
        gcongr with h j
        have hA : cexΔ.A j = {()} := rfl
        rw [hA, Finset.sum_singleton, cexΔ_σ, mul_one]
        calc MDC.histProb cexθ i t h j * ENNReal.ofReal (cexΔ.C j ())
            ≤ MDC.histProb cexθ i t h j * 1 := by
              gcongr
              simp only [cexΔ, CTMDC.aux, cexΨ]
              split_ifs <;> norm_num
          _ = _ := mul_one _
    _ = n := by simp

lemma cexΔ_avgValue_zero (i : ℕ) (hi : 2 ≤ i) : cexΔ.avgValue i ≤ 0 := by
  refine le_trans (iInf_le _ cexθ) ?_
  unfold MDC.avgCost
  have : ∀ t, MDC.expectedCost cexθ i t = 0 := by
    intro t
    unfold MDC.expectedCost
    apply ENNReal.tsum_eq_zero.mpr; intro h
    apply ENNReal.tsum_eq_zero.mpr; intro j
    apply Finset.sum_eq_zero; intro a _
    by_cases hj : j ≤ 1
    · rw [cex_zero cexθ i hi t h j hj]; simp
    · have : cexΔ.C j a = 0 := by simp only [cexΔ, CTMDC.aux, cexΨ]; rw [if_neg hj]; ring
      rw [this]; simp
  simp [this]

lemma cex_CTAC : cexΨ.CTAC (1/2) := by
  intro i
  by_cases hi : i ≤ 1
  · exact (cexΔ_avgValue_le i).trans (cex_avgValue_ge i hi)
  · exact (cexΔ_avgValue_zero i (by omega)).trans (by simp)

noncomputable def cexPN (N i : ℕ) (_ : Unit) (j : ℕ) : ℝ≥0∞ :=
  if i ≤ 1 then
    (if j = i then ENNReal.ofReal (1/2) else if j = cexPartner i then ENNReal.ofReal (1/2 - 1/N)
      else if j = N then ENNReal.ofReal (1/N) else 0)
  else if i + 1 < N then
    (if j = i then ENNReal.ofReal (1/2) else if j = cexPartner i then ENNReal.ofReal (1/2) else 0)
  else (if j = i then 1 else 0)

noncomputable def cexAS : ApproxSeq cexΔ where
  N0 := 3
  SN N := Finset.range (N + 1)
  SN_nonempty N _ := ⟨0, by simp⟩
  SN_mono N N' _ h := Finset.range_subset_range.mpr (by omega)
  SN_cover i := ⟨i + 3, by omega, by simp⟩
  PN := cexPN
  PN_sum := by
    intro N hN i hi a _
    simp only [Finset.mem_range] at hi
    have hp := cexPartner_ne i
    have hpl := @cexPartner_le i
    unfold cexPN
    by_cases h1 : i ≤ 1
    · simp only [h1, if_true]
      have hps := cexPartner_small h1
      rw [Finset.sum_congr rfl (g := fun j => (if j = i then ENNReal.ofReal (1/2) else 0) +
        (if j = cexPartner i then ENNReal.ofReal (1/2 - 1/N) else 0) +
        (if j = N then ENNReal.ofReal (1/N) else 0)) (fun j _ => by
          split_ifs <;> first | omega | simp)]
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq',
        Finset.sum_ite_eq']
      rw [if_pos (by simp; omega), if_pos (by simp; omega), if_pos (by simp)]
      have hN' : (2:ℝ) ≤ N := by exact_mod_cast (show 2 ≤ N by omega)
      have h3 : (0:ℝ) ≤ 1/2 - 1/N := by
        rw [sub_nonneg, div_le_div_iff₀ (by positivity) (by positivity)]; linarith
      rw [← ENNReal.ofReal_add (by norm_num) h3, ← ENNReal.ofReal_add (by positivity) (by positivity)]
      norm_num; ring
    · simp only [h1, if_false]
      by_cases h2 : i + 1 < N
      · simp only [h2, if_true]
        rw [Finset.sum_congr rfl (g := fun j => (if j = i then ENNReal.ofReal (1/2) else 0) +
          (if j = cexPartner i then ENNReal.ofReal (1/2) else 0)) (fun j _ => by
            split_ifs <;> first | omega | simp)]
        rw [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq']
        rw [if_pos (by simp; omega), if_pos (by simp; omega)]
        rw [← ENNReal.ofReal_add (by norm_num) (by norm_num)]
        norm_num
      · simp only [h2, if_false]
        rw [Finset.sum_ite_eq']
        simp; omega
  PN_lim := by
    intro i a _ j
    rw [show a = () from rfl, cexΔ_P]
    have hp := cexPartner_ne i
    by_cases h1 : i ≤ 1
    · by_cases hj : j = i
      · simp only [cexPN, h1, hj, if_true]; exact tendsto_const_nhds
      · by_cases hj2 : j = cexPartner i
        · simp only [cexPN, h1, hj, hj2, hp, if_true, if_false]
          apply ENNReal.tendsto_ofReal
          have := (tendsto_const_div_atTop_nhds_zero_nat (1:ℝ)).const_sub (1/2 : ℝ)
          simpa using this
        · simp only [hj, hj2, if_false]
          apply tendsto_const_nhds.congr'
          filter_upwards [eventually_gt_atTop j] with N hN
          simp only [cexPN, h1, hj, hj2, if_true, if_false]
          rw [if_neg (by omega)]
    · apply tendsto_const_nhds.congr'
      filter_upwards [eventually_gt_atTop (i + 1)] with N hN
      simp only [cexPN, h1, if_false, if_pos hN]

noncomputable def cexrN (N j : ℕ) : ℝ := if j = N then -(N : ℝ) else 0

lemma cexrN_ev (i : ℕ) : ∀ᶠ N in atTop, cexrN N i = 0 := by
  filter_upwards [eventually_gt_atTop i] with N hN
  simp [cexrN, (show i ≠ N by omega)]

lemma cex_AC : cexAS.AC (fun _ => 0) cexrN := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro N hN i hi
    refine ⟨by simp [cexΔ, CTMDC.aux, cexΨ], ?_⟩
    have hA : cexΔ.A i = {()} := rfl
    simp only [hA, Finset.inf'_singleton, ApproxSeq.bracket]
    change 3 ≤ N at hN
    change i ∈ Finset.range (N + 1) at hi
    simp only [Finset.mem_range] at hi
    rw [Finset.sum_eq_single N]
    · have hp := cexPartner_ne i
      have hpl := @cexPartner_le i
      simp only [cexAS, cexPN, cexrN, cexΔ, CTMDC.aux, cexΨ]
      by_cases h1 : i ≤ 1
      · have hps := cexPartner_small h1
        simp only [h1, if_true, if_neg (show N ≠ i by omega), if_neg (show N ≠ cexPartner i by omega),
          if_neg (show i ≠ N by omega)]
        rw [ENNReal.toReal_ofReal (by positivity)]
        have : (N:ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
        field_simp; ring
      · simp only [h1, if_false]
        by_cases h2 : i + 1 < N
        · simp only [h2, if_true, if_neg (show N ≠ i by omega), if_neg (show N ≠ cexPartner i by omega),
            if_neg (show i ≠ N by omega)]
          simp
        · simp only [h2, if_false]
          by_cases h3 : i = N
          · subst h3; simp
          · simp [h3, Ne.symm h3]
    · intro b _ hb; simp [cexrN, hb]
    · intro h; exact (h (Finset.mem_range.mpr (by omega))).elim
  · intro i
    rw [limsup_congr ((cexrN_ev i).mono fun N h => by rw [h])]
    simp
  · refine ⟨0, le_refl _, fun i => ?_⟩
    rw [liminf_congr ((cexrN_ev i).mono fun N h => by rw [h])]
    simp
  · simp
  · intro i
    simp only [EReal.coe_zero, limsup_const]
    exact EReal.coe_ennreal_nonneg _

theorem cex_core : ¬ (∀ {S Act : Type} [Countable S] (Ψ : CTMDC S Act) (hΨ : Ψ.IsValid)
    (tau B : ℝ) (hCTB : Ψ.CTB tau B) (hCTAC : Ψ.CTAC tau)
    (Δs : ApproxSeq (Ψ.aux tau)) (JN : ℕ → ℝ) (rN : ℕ → S → ℝ) (hAC : Δs.AC JN rN),
    (∃ Jstar : ℝ, Tendsto JN atTop (𝓝 Jstar) ∧
        ∀ i, (((Ψ.aux tau).avgValue i : ℝ≥0∞) : EReal) = (Jstar : EReal) ∧
          ((Ψ.avgValue i : ℝ≥0∞) : EReal) = (Jstar : EReal)) ∧
      ∀ (eN : ℕ → S → Act) (estar : S → Act),
        Δs.RealizesMin JN rN eN → Δs.IsLimitPoint eN estar →
          ∃ he : ∀ i, estar i ∈ Ψ.A i,
            (∀ i, (Ψ.aux tau).avgCost ((Ψ.aux tau).ofStationary estar he) i =
                (Ψ.aux tau).avgValue i) ∧
            ∀ i, Ψ.avgCost (Ψ.ofStationary estar he) i = Ψ.avgValue i) := by
  intro H
  obtain ⟨⟨J, hJ, hval⟩, -⟩ := H cexΨ cex_valid (1/2) 1 cex_CTB cex_CTAC cexAS (fun _ => 0) cexrN cex_AC
  have hJ0 : J = 0 := tendsto_nhds_unique hJ tendsto_const_nhds
  have h0 := (hval 0).2
  rw [hJ0, EReal.coe_zero, EReal.coe_ennreal_eq_zero] at h0
  have := cex_avgValue_ge 0 (by norm_num)
  rw [h0] at this
  exact absurd this (by norm_num)

end SennottDP.ContinuousTime

open SennottDP.ContinuousTime

theorem solution : ¬ (∀ {S Act : Type} [Countable S] (Ψ : CTMDC S Act) (hΨ : Ψ.IsValid)
    (tau B : ℝ) (hCTB : Ψ.CTB tau B) (hCTAC : Ψ.CTAC tau)
    (Δs : ApproxSeq (Ψ.aux tau)) (JN : ℕ → ℝ) (rN : ℕ → S → ℝ) (hAC : Δs.AC JN rN),
    (∃ Jstar : ℝ, Tendsto JN atTop (𝓝 Jstar) ∧
        ∀ i, (((Ψ.aux tau).avgValue i : ℝ≥0∞) : EReal) = (Jstar : EReal) ∧
          ((Ψ.avgValue i : ℝ≥0∞) : EReal) = (Jstar : EReal)) ∧
      ∀ (eN : ℕ → S → Act) (estar : S → Act),
        Δs.RealizesMin JN rN eN → Δs.IsLimitPoint eN estar →
          ∃ he : ∀ i, estar i ∈ Ψ.A i,
            (∀ i, (Ψ.aux tau).avgCost ((Ψ.aux tau).ofStationary estar he) i =
                (Ψ.aux tau).avgValue i) ∧
            ∀ i, Ψ.avgCost (Ψ.ofStationary estar he) i = Ψ.avgValue i) :=
  cex_core
