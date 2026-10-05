import Mathlib
import Definitions.Def_ProcessingNetworks_PacketNetworks_ProcessesAndFluidModel
import Definitions.Def_ProcessingNetworks_PacketNetworks_AmbientChain



namespace ProcessingNetworks.PacketNetworks

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal

namespace PNCex

universe u

noncomputable def pr (n : ℕ) : ℝ := 1 / (((n : ℝ) + 1) * ((n : ℝ) + 2))

lemma pr_nonneg (n : ℕ) : 0 ≤ pr n := by unfold pr; positivity

lemma pr_partial (N : ℕ) : ∑ n ∈ Finset.range N, pr n = 1 - 1 / ((N : ℝ) + 1) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, ih]; unfold pr; push_cast
    field_simp; ring

lemma pr_hasSum : HasSum pr 1 := by
  rw [hasSum_iff_tendsto_nat_of_nonneg pr_nonneg]
  simp_rw [pr_partial]
  have := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  have h2 := (tendsto_const_nhds (x := (1:ℝ))).sub this
  simpa using h2

noncomputable def pmfN : PMF ℕ := ⟨fun n => ENNReal.ofReal (pr n), by
  have h := ENNReal.ofReal_tsum_of_nonneg pr_nonneg pr_hasSum.summable
  rw [pr_hasSum.tsum_eq, ENNReal.ofReal_one] at h
  rw [h]; exact ENNReal.summable.hasSum⟩

lemma pmfN_apply (n : ℕ) : pmfN n = ENNReal.ofReal (pr n) := rfl

lemma pmfN_pos (n : ℕ) : 0 < pmfN n := by
  rw [pmfN_apply, ENNReal.ofReal_pos]; unfold pr; positivity

noncomputable def μA : Measure (ULift.{u} ℕ) := pmfN.toMeasure.map ULift.up

instance : IsProbabilityMeasure (μA.{u}) := by
  unfold μA; exact Measure.isProbabilityMeasure_map measurable_up.aemeasurable

noncomputable def μU : Measure ℝ := volume.restrict (Set.Ioo (0:ℝ) 1)

instance : IsProbabilityMeasure μU := ⟨by simp [μU, Real.volume_Ioo]⟩

abbrev Ωc : Type u := (ℕ → ULift.{u} ℕ) × (ℕ → ℝ)

noncomputable instance msΩ : MeasureSpace Ωc.{u} :=
  ⟨(Measure.infinitePi (fun _ : ℕ => μA.{u})).prod (Measure.infinitePi (fun _ : ℕ => μU))⟩

instance : IsProbabilityMeasure (ℙ : Measure Ωc.{u}) := by
  change IsProbabilityMeasure ((Measure.infinitePi (fun _ : ℕ => μA.{u})).prod
    (Measure.infinitePi (fun _ : ℕ => μU)))
  infer_instance

lemma vol_eq : (ℙ : Measure Ωc.{u}) = (Measure.infinitePi (fun _ : ℕ => μA.{u})).prod
    (Measure.infinitePi (fun _ : ℕ => μU)) := rfl

lemma map_fst : (ℙ : Measure Ωc.{u}).map Prod.fst = Measure.infinitePi (fun _ : ℕ => μA.{u}) := by
  rw [vol_eq, Measure.map_fst_prod]; simp

lemma map_snd : (ℙ : Measure Ωc.{u}).map Prod.snd = Measure.infinitePi (fun _ : ℕ => μU) := by
  rw [vol_eq, Measure.map_snd_prod]; simp

lemma iIndep_comp {α α' β : Type*} [MeasurableSpace α] [MeasurableSpace α'] [MeasurableSpace β]
    (μ : Measure α) [IsProbabilityMeasure μ] (h : α → α') (hh : Measurable h)
    (X : ℕ → α' → β) (hX : ∀ i, Measurable (X i)) (H : iIndepFun X (μ.map h)) :
    iIndepFun (fun i ω => X i (h ω)) μ := by
  have : IsProbabilityMeasure (μ.map h) := Measure.isProbabilityMeasure_map hh.aemeasurable
  rw [iIndepFun_iff_map_fun_eq_infinitePi_map (X := fun i ω => X i (h ω))
    (fun i => (hX i).comp hh)]
  have H2 := (iIndepFun_iff_map_fun_eq_infinitePi_map hX).1 H
  rw [Measure.map_map (measurable_pi_iff.2 hX) hh] at H2
  convert H2 using 2
  · rfl
  · funext i
    rw [Measure.map_map (hX i) hh]; rfl

/-- generic: independence of a function of shifted coordinates of the first factor -/
lemma indep_fst {β : Type*} [MeasurableSpace β] (g : ULift.{u} ℕ → β) (hg : Measurable g) :
    iIndepFun (fun (τ : ℕ) (ω : Ωc.{u}) => g (ω.1 (τ + 1))) ℙ := by
  refine iIndep_comp (ℙ : Measure Ωc.{u}) Prod.fst measurable_fst
    (fun τ a => g (a (τ + 1))) (fun τ => hg.comp (measurable_pi_apply _)) ?_
  rw [map_fst]
  exact (iIndepFun_infinitePi (P := fun _ : ℕ => μA.{u}) (X := fun _ => g) (fun _ => hg)).precomp
    (g := fun τ => τ + 1) (fun a b h => by simpa using h)

lemma indep_snd {β : Type*} [MeasurableSpace β] (g : ℝ → β) (hg : Measurable g) :
    iIndepFun (fun (τ : ℕ) (ω : Ωc.{u}) => g (ω.2 (τ + 1))) ℙ := by
  refine iIndep_comp (ℙ : Measure Ωc.{u}) Prod.snd measurable_snd
    (fun τ a => g (a (τ + 1))) (fun τ => hg.comp (measurable_pi_apply _)) ?_
  rw [map_snd]
  exact (iIndepFun_infinitePi (P := fun _ : ℕ => μU) (X := fun _ => g) (fun _ => hg)).precomp
    (g := fun τ => τ + 1) (fun a b h => by simpa using h)

lemma law_fst (τ : ℕ) : (ℙ : Measure Ωc.{u}).map (fun ω => ω.1 τ) = μA.{u} := by
  have : (fun ω : Ωc.{u} => ω.1 τ) = (fun a : ℕ → ULift.{u} ℕ => a τ) ∘ Prod.fst := rfl
  rw [this, ← Measure.map_map (measurable_pi_apply _) measurable_fst, map_fst,
    Measure.infinitePi_map_eval]

lemma law_snd (τ : ℕ) : (ℙ : Measure Ωc.{u}).map (fun ω => ω.2 τ) = μU := by
  have : (fun ω : Ωc.{u} => ω.2 τ) = (fun a : ℕ → ℝ => a τ) ∘ Prod.snd := rfl
  rw [this, ← Measure.map_map (measurable_pi_apply _) measurable_snd, map_snd,
    Measure.infinitePi_map_eval]

lemma indep_cross : Indep (MeasurableSpace.comap (Prod.fst : Ωc.{u} → _) inferInstance)
    (MeasurableSpace.comap (Prod.snd : Ωc.{u} → _) inferInstance) ℙ := by
  have := indepFun_prod (μ := Measure.infinitePi (fun _ : ℕ => μA.{u}))
    (ν := Measure.infinitePi (fun _ : ℕ => μU)) (X := id) (Y := id) measurable_id measurable_id
  rw [IndepFun_iff_Indep] at this
  exact this


lemma meas_ulift {β : Type*} [MeasurableSpace β] (g : ULift.{u} ℕ → β) : Measurable g :=
  fun _ _ => MeasurableSet.of_discrete (α := ℕ)

lemma not_summable_npr : ¬ Summable (fun n : ℕ => (n : ℝ) * pr n) := by
  intro hs
  have hs1 := (summable_nat_add_iff 1).2 hs
  have hharm : ¬ Summable (fun n : ℕ => 1 / ((n : ℝ) + 2)) := by
    intro h
    have := (summable_nat_add_iff (f := fun n : ℕ => 1 / (n : ℝ)) 2).1 (by
      refine h.congr fun n => ?_; push_cast; ring_nf)
    exact Real.not_summable_one_div_natCast this
  apply hharm
  have h3 : Summable (fun n : ℕ => 3 * (((n + 1 : ℕ) : ℝ) * pr (n + 1))) := hs1.mul_left 3
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) h3
  unfold pr; push_cast
  rw [div_le_iff₀ (by positivity)]
  field_simp
  nlinarith

lemma not_integrable_pmf : ¬ Integrable (fun n : ℕ => (n : ℝ)) pmfN.toMeasure := by
  intro hi
  have h := hi.2
  unfold HasFiniteIntegral at h
  rw [lintegral_countable'] at h
  apply not_summable_npr
  have heq : ∀ n : ℕ, ‖(n : ℝ)‖ₑ * pmfN.toMeasure {n} = ENNReal.ofReal ((n : ℝ) * pr n) := by
    intro n
    rw [PMF.toMeasure_apply_singleton _ _ (MeasurableSet.singleton n), pmfN_apply,
      ENNReal.ofReal_mul (by positivity)]
    congr 1
    rw [Real.enorm_eq_ofReal (by positivity)]
  simp_rw [heq] at h
  have h2 := ENNReal.tsum_coe_ne_top_iff_summable.1 h.ne
  have h3 := NNReal.summable_coe.2 h2
  refine h3.congr fun n => ?_
  simp only [Real.coe_toNNReal _ (mul_nonneg (Nat.cast_nonneg n) (pr_nonneg n))]


noncomputable def Pc : PacketPrimitives 1 1 Ωc.{u} where
  f := fun z _ => fun _ => if 1 ≤ z 0 then 1 else 0
  Eincr := fun τ ω => fun _ => (ω.1 τ).down
  U := fun τ ω => ω.2 τ

lemma not_integrable_E : ¬ Integrable (fun ω : Ωc.{u} => ((ω.1 1).down : ℝ)) ℙ := by
  intro hi
  have h1 : Integrable (fun a : ULift.{u} ℕ => (a.down : ℝ)) μA.{u} := by
    rw [← law_fst 1]
    exact (integrable_map_measure (meas_ulift _).aestronglyMeasurable
      (measurable_pi_apply 1 |>.comp measurable_fst).aemeasurable).2 hi
  unfold μA at h1
  have h2 := (integrable_map_measure (meas_ulift _).aestronglyMeasurable
      measurable_up.aemeasurable).1 h1
  exact not_integrable_pmf h2

lemma law_E (τ : ℕ) : (ℙ : Measure Ωc.{u}).map (Pc.Eincr τ) =
    μA.{u}.map (fun a : ULift.{u} ℕ => fun _ : Fin 1 => a.down) := by
  have : Pc.Eincr τ = (fun a : ULift.{u} ℕ => fun _ : Fin 1 => a.down) ∘ (fun ω : Ωc.{u} => ω.1 τ) :=
    rfl
  rw [this, ← Measure.map_map (meas_ulift _) (measurable_pi_apply τ |>.comp measurable_fst),
    law_fst]

lemma measE (τ : ℕ) : Measurable (Pc.{u}.Eincr τ) :=
  (meas_ulift (fun a : ULift.{u} ℕ => fun _ : Fin 1 => a.down)).comp
    (measurable_pi_apply τ |>.comp measurable_fst)

lemma measU (τ : ℕ) : Measurable (Pc.{u}.U τ) := measurable_pi_apply τ |>.comp measurable_snd

lemma PA : PrimitiveAssumptions Pc.{u} (fun _ => 0) where
  arrivals_indep := indep_fst (fun a : ULift.{u} ℕ => fun _ : Fin 1 => a.down) (meas_ulift _)
  arrivals_ident := fun τ => ⟨(measE _).aemeasurable, (measE _).aemeasurable, by
    rw [law_E, law_E]⟩
  classes_indep := iIndepFun.of_subsingleton
  arrival_mean := fun i => integral_undef not_integrable_E
  arrival_zero := by
    have hm : MeasurableSet {ω : Ωc.{u} | Pc.Eincr 1 ω = 0} :=
      measE 1 (MeasurableSet.singleton (0 : Fin 1 → ℕ))
    have e1 : ℙ {ω : Ωc.{u} | Pc.Eincr 1 ω = 0} =
        (ℙ : Measure Ωc.{u}).map (Pc.Eincr 1) {(0 : Fin 1 → ℕ)} := by
      rw [Measure.map_apply (measE 1) (MeasurableSet.singleton _)]; rfl
    rw [e1, law_E, Measure.map_apply (meas_ulift _) (MeasurableSet.singleton _)]
    unfold μA
    rw [Measure.map_apply measurable_up (meas_ulift _ (MeasurableSet.singleton _))]
    refine lt_of_lt_of_le (pmfN_pos 0) ?_
    rw [← PMF.toMeasure_apply_singleton _ _ (MeasurableSet.singleton 0)]
    apply measure_mono
    intro n hn
    simp only [Set.mem_singleton_iff] at hn
    subst hn
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    rfl
  uniform := fun τ => law_snd (τ + 1)
  uniform_indep := indep_snd id measurable_id
  arrivals_uniform_indep := by
    refine indep_of_indep_of_le_right (indep_of_indep_of_le_left indep_cross ?_) ?_
    · refine iSup_le fun τ => ?_
      rw [show Pc.{u}.Eincr (τ + 1) = (fun a : ℕ → ULift.{u} ℕ => fun _ : Fin 1 => (a (τ+1)).down)
        ∘ Prod.fst from rfl, ← MeasurableSpace.comap_comp]
      have hm : Measurable (fun a : ℕ → ULift.{u} ℕ => fun _ : Fin 1 => (a (τ+1)).down) :=
        (meas_ulift (fun b : ULift.{u} ℕ => fun _ : Fin 1 => b.down)).comp (measurable_pi_apply _)
      exact MeasurableSpace.comap_mono hm.comap_le
    · refine iSup_le fun τ => ?_
      rw [show Pc.{u}.U (τ + 1) = (fun a : ℕ → ℝ => a (τ+1)) ∘ Prod.snd from rfl,
        ← MeasurableSpace.comap_comp]
      exact MeasurableSpace.comap_mono (measurable_pi_apply _).comap_le
  policy_measurable := fun z => measurable_const


noncomputable def gY (a : ULift.{u} ℕ) : ℝ := if 1 ≤ a.down then 1 else 0

noncomputable def Yv (i : ℕ) (ω : Ωc.{u}) : ℝ := gY (ω.1 (i + 1))

lemma measY (i : ℕ) : Measurable (Yv.{u} i) :=
  (meas_ulift gY).comp (measurable_pi_apply _ |>.comp measurable_fst)

lemma lawY (i : ℕ) : (ℙ : Measure Ωc.{u}).map (Yv i) = μA.{u}.map gY := by
  have : Yv.{u} i = gY ∘ (fun ω : Ωc.{u} => ω.1 (i + 1)) := rfl
  rw [this, ← Measure.map_map (meas_ulift _) (measurable_pi_apply _ |>.comp measurable_fst),
    law_fst]

lemma Y_nonneg (i : ℕ) (ω : Ωc.{u}) : 0 ≤ Yv i ω := by
  unfold Yv gY; split_ifs <;> norm_num

lemma Y_le (i : ℕ) (ω : Ωc.{u}) : Yv i ω ≤ 1 := by
  unfold Yv gY; split_ifs <;> norm_num

lemma intY : Integrable (Yv.{u} 0) ℙ :=
  Integrable.of_bound (measY 0).aestronglyMeasurable 1
    (ae_of_all _ fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (Y_nonneg 0 ω)]; exact Y_le 0 ω)

lemma meanY_pos : 0 < ∫ ω, Yv.{u} 0 ω ∂ℙ := by
  rw [integral_pos_iff_support_of_nonneg (fun ω => Y_nonneg 0 ω) intY]
  have hsub : (fun ω : Ωc.{u} => ω.1 1) ⁻¹' {ULift.up 1} ⊆ Function.support (Yv.{u} 0) := by
    intro ω hω
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at hω
    simp [Function.mem_support, Yv, gY, hω]
  refine lt_of_lt_of_le ?_ (measure_mono hsub)
  have hmeas : Measurable (fun ω : Ωc.{u} => ω.1 1) := measurable_pi_apply 1 |>.comp measurable_fst
  rw [← Measure.map_apply hmeas (MeasurableSet.of_discrete (α := ℕ)), law_fst]
  unfold μA
  rw [Measure.map_apply measurable_up (MeasurableSet.of_discrete (α := ℕ))]
  refine lt_of_lt_of_le (pmfN_pos 1) ?_
  rw [← PMF.toMeasure_apply_singleton _ _ (MeasurableSet.singleton 1)]
  apply measure_mono
  intro n hn
  simp only [Set.mem_singleton_iff] at hn
  subst hn
  simp

lemma sumIcc (h : ℕ → ℝ) (n : ℕ) :
    ∑ ℓ ∈ Finset.Icc 1 n, h ℓ = ∑ i ∈ Finset.range n, h (i + 1) := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_Icc_succ_top (by omega), ih, Finset.sum_range_succ]

lemma Y_le_E (n : ℕ) (ω : Ωc.{u}) :
    ∑ i ∈ Finset.range n, Yv i ω ≤ (Ecum Pc.{u} n ω 0 : ℝ) := by
  unfold Ecum; push_cast
  rw [sumIcc (fun ℓ => (((Pc.{u}.Eincr ℓ ω 0 : ℕ)) : ℝ))]
  refine Finset.sum_le_sum fun i _ => ?_
  unfold Yv gY Pc; dsimp only
  split_ifs with h
  · exact_mod_cast h
  · positivity

lemma slln_fails : ∀ᵐ ω ∂(ℙ : Measure Ωc.{u}), ¬ SLLNHoldsAt Pc.{u} (fun _ => 0) ω := by
  have hindep : Pairwise (fun i j => IndepFun (Yv.{u} i) (Yv.{u} j) ℙ) :=
    fun i j hij => (indep_fst gY (meas_ulift _)).indepFun hij
  have hident : ∀ i, IdentDistrib (Yv.{u} i) (Yv.{u} 0) ℙ ℙ :=
    fun i => ⟨(measY i).aemeasurable, (measY 0).aemeasurable, by rw [lawY, lawY]⟩
  have hlaw := strong_law_ae_real (Yv.{u}) intY hindep hident
  filter_upwards [hlaw] with ω hω hS
  set m := ∫ ω, Yv.{u} 0 ω ∂ℙ with hmdef
  have hm : 0 < m := meanY_pos
  obtain ⟨Nb, hNb⟩ := hS 1 one_pos (m / 2) (half_pos hm)
  have ev := (hω.eventually (lt_mem_nhds (half_lt_self hm))).and
    ((eventually_ge_atTop ⌈Nb⌉₊).and (eventually_ge_atTop 1))
  obtain ⟨n, h1, h2, h3⟩ := ev.exists
  have hb := hNb n (le_trans (Nat.le_ceil Nb) (by exact_mod_cast h2)) 1 ⟨zero_le_one, le_rfl⟩ 0
  rw [mul_one, Nat.floor_natCast, zero_mul, sub_zero] at hb
  have hle := Y_le_E n ω
  have hn : (0 : ℝ) < n := by exact_mod_cast h3
  have : (∑ i ∈ Finset.range n, Yv i ω) / n ≤ (n : ℝ)⁻¹ * (Ecum Pc.{u} n ω 0 : ℝ) := by
    rw [div_eq_inv_mul]; exact mul_le_mul_of_nonneg_left hle (by positivity)
  have := lt_of_le_of_lt (le_abs_self _) hb
  linarith

lemma slln_cex : ¬ (∀ᵐ ω ∂(ℙ : Measure Ωc.{u}), SLLNHoldsAt Pc.{u} (fun _ => 0) ω) := by
  intro h
  have h2 := h.and slln_fails
  obtain ⟨ω, h3, h4⟩ := h2.exists
  exact h4 h3


def datc : PacketNetworkData 1 1 := ⟨fun _ => 0, fun _ => none⟩

def sch (z : Fin 1 → ℕ) : ℕ := if 1 ≤ z 0 then 1 else 0

lemma sch_le (z : Fin 1 → ℕ) : sch z ≤ z 0 := by unfold sch; split_ifs <;> omega

noncomputable def jumpc (z : Fin 1 → ℕ) : PMF (Fin 1 → ℕ) :=
  pmfN.map (fun n => fun _ => z 0 + n - sch z)

lemma probE (e : Fin 1 → ℕ) : ℙ {ω : Ωc.{u} | Pc.Eincr 1 ω = e} = pmfN (e 0) := by
  have e1 : ℙ {ω : Ωc.{u} | Pc.Eincr 1 ω = e} =
      (ℙ : Measure Ωc.{u}).map (Pc.Eincr 1) {e} := by
    rw [Measure.map_apply (measE 1) (MeasurableSet.singleton _)]; rfl
  rw [e1, law_E, Measure.map_apply (meas_ulift _) (MeasurableSet.singleton _)]
  unfold μA
  rw [Measure.map_apply measurable_up (meas_ulift _ (MeasurableSet.singleton _))]
  rw [← PMF.toMeasure_apply_singleton _ _ (MeasurableSet.singleton (e 0))]
  congr 1
  ext n
  simp only [Set.mem_preimage, Set.mem_singleton_iff]
  constructor
  · intro h; rw [← h]
  · intro h; funext i; rw [Fin.fin_one_eq_zero i, h]

lemma next_eq (z : Fin 1 → ℤ) (e : Fin 1 → ℕ) (s : Fin 1 → ℕ) :
    nextState datc z e s 0 = z 0 + e 0 - s 0 := by
  simp [nextState, Rint, datc]

lemma policyChain : IsPolicyChain datc Pc.{u} jumpc := by
  intro z y
  have hf : ∀ u, Pc.{u}.f z u = fun _ => sch z := fun _ => rfl
  simp only [hf]
  rw [lintegral_const, Measure.restrict_apply_univ, Real.volume_Ioo, sub_zero,
    ENNReal.ofReal_one, mul_one]
  rw [← (Equiv.funUnique (Fin 1) ℕ).symm.tsum_eq]
  unfold jumpc
  rw [PMF.map_apply]
  refine tsum_congr fun n => ?_
  have hs := sch_le z
  by_cases hc : y = fun _ => z 0 + n - sch z
  · rw [if_pos hc, if_pos, probE]
    · rfl
    · funext i
      rw [Fin.fin_one_eq_zero i, next_eq, hc]
      simp only [Equiv.funUnique_symm_apply, uniqueElim_const]
      push_cast [hs, show sch z ≤ z 0 + n by omega]; ring
  · rw [if_neg hc, if_neg]
    intro h
    apply hc
    have h0 := congrFun h 0
    rw [next_eq] at h0
    simp only [Equiv.funUnique_symm_apply, uniqueElim_const] at h0
    funext i; rw [Fin.fin_one_eq_zero i]
    omega


def Sc : Finset (Fin 1 → ℕ) := {fun _ => 0, fun _ => 1}

lemma h121c : SatisfiesAssumption121 datc :=
  ⟨fun i => ⟨0, Subsingleton.elim _ _⟩, fun n js hc => by
    have := hc 0; simp [datc] at this⟩

lemma hadmc : IsAdmissibleMarkovianPolicy datc Sc Pc.{u}.f := by
  intro z uu _ _
  refine ⟨?_, fun i => ?_⟩
  · change (fun _ => sch z) ∈ Sc
    unfold sch Sc; split_ifs <;> simp
  · rw [Fin.fin_one_eq_zero i]
    change (∑ j, B datc 0 j * ((sch z : ℕ) : ℝ)) ≤ (z 0 : ℝ)
    simp only [B, datc, Fin.sum_univ_one, if_true, one_mul]
    exact_mod_cast sch_le z

lemma jump_supp (z y : Fin 1 → ℕ) (h : z 0 ≤ y 0 + 1) : y ∈ (jumpc z).support := by
  unfold jumpc
  rw [PMF.mem_support_map_iff]
  refine ⟨y 0 + sch z - z 0, ?_, ?_⟩
  · rw [PMF.mem_support_iff]; exact (pmfN_pos _).ne'
  · funext i; rw [Fin.fin_one_eq_zero i]
    have := sch_le z
    unfold sch at *; split_ifs at * <;> omega

lemma jump_supp_ge (z y : Fin 1 → ℕ) (h : y ∈ (jumpc z).support) : z 0 ≤ y 0 + 1 := by
  unfold jumpc at h
  rw [PMF.mem_support_map_iff] at h
  obtain ⟨n, _, hn⟩ := h
  rw [← hn]
  show z 0 ≤ z 0 + n - sch z + 1
  have := sch_le z
  unfold sch at *; split_ifs at * <;> omega

lemma reach (k : ℕ) : ∀ x y : Fin 1 → ℕ, x 0 ≤ k → ∃ n, y ∈ (stepIter jumpc n x).support := by
  induction k with
  | zero =>
    intro x y hx
    refine ⟨1, ?_⟩
    change y ∈ ((jumpc x).bind (Stability.stepIter jumpc 0)).support
    rw [PMF.mem_support_bind_iff]
    exact ⟨y, jump_supp x y (by omega), by simp [Stability.stepIter]⟩
  | succ k ih =>
    intro x y hx
    by_cases h : x 0 ≤ y 0 + 1
    · refine ⟨1, ?_⟩
      change y ∈ ((jumpc x).bind (Stability.stepIter jumpc 0)).support
      rw [PMF.mem_support_bind_iff]
      exact ⟨y, jump_supp x y h, by simp [Stability.stepIter]⟩
    · obtain ⟨n, hn⟩ := ih (fun _ => x 0 - 1) y (by show x 0 - 1 ≤ k; omega)
      refine ⟨n + 1, ?_⟩
      change y ∈ ((jumpc x).bind (Stability.stepIter jumpc n)).support
      rw [PMF.mem_support_bind_iff]
      exact ⟨fun _ => x 0 - 1, jump_supp x _ (by show x 0 ≤ x 0 - 1 + 1; omega), hn⟩

lemma irrc : Irreducible jumpc := by
  intro x y
  obtain ⟨n, hn⟩ := reach (x 0) x y le_rfl
  exact ⟨n, pos_iff_ne_zero.2 ((PMF.mem_support_iff _ _).1 hn)⟩


def x0 : Fin 1 → ℕ := fun _ => 0

lemma jump0 (y : Fin 1 → ℕ) : jumpc x0 y = pmfN (y 0) := by
  unfold jumpc
  rw [PMF.map_apply, tsum_eq_single (y 0)]
  · rw [if_pos]; funext i; rw [Fin.fin_one_eq_zero i]; simp [x0, sch]
  · intro n hn
    rw [if_neg]
    intro h; apply hn; have := congrFun h 0; simp [x0, sch] at this; omega

noncomputable def tab (n : ℕ) (y : Fin 1 → ℕ) : ℝ≥0∞ := Stability.tabooProb jumpc x0 n y

noncomputable def T (n m : ℕ) : ℝ≥0∞ := ∑' y : Fin 1 → ℕ, if m ≤ y 0 then tab n y else 0

lemma ne_x0 {m : ℕ} (hm : 1 ≤ m) {y : Fin 1 → ℕ} (hy : m ≤ y 0) : y ≠ x0 := by
  intro h; rw [h] at hy; simp [x0] at hy; omega

def eq1 : ℕ ≃ (Fin 1 → ℕ) := ⟨fun k _ => k, fun y => y 0, fun _ => rfl, fun y => by
  funext i; rw [Fin.fin_one_eq_zero i]⟩

lemma T_one (m : ℕ) (hm : 1 ≤ m) : T 1 m = ∑' k : ℕ, if m ≤ k then pmfN k else 0 := by
  unfold T
  rw [← eq1.tsum_eq]
  refine tsum_congr fun k => ?_
  change (if m ≤ k then tab 1 (fun _ => k) else 0) = _
  split_ifs with h
  · unfold tab
    simp only [Stability.tabooProb]
    rw [if_neg (ne_x0 hm (y := fun _ => k) h)]
    rw [tsum_eq_single x0]
    · simp [jump0]
    · intro z hz; simp [hz]
  · rfl

lemma T_step (n m : ℕ) (hm : 1 ≤ m) : T n (m + 1) ≤ T (n + 1) m := by
  have h1 : T (n + 1) m = ∑' y : Fin 1 → ℕ,
      if m ≤ y 0 then ∑' z, tab n z * jumpc z y else 0 := by
    unfold T
    refine tsum_congr fun y => ?_
    split_ifs with h
    · unfold tab; simp only [Stability.tabooProb]; rw [if_neg (ne_x0 hm h)]
    · rfl
  have h2 : ∀ y : Fin 1 → ℕ, (∑' z, (if m + 1 ≤ z 0 then tab n z else 0) * jumpc z y) ≤
      if m ≤ y 0 then ∑' z, tab n z * jumpc z y else 0 := by
    intro y
    split_ifs with h
    · refine ENNReal.tsum_le_tsum fun z => ?_
      split_ifs <;> simp
    · apply le_of_eq
      refine ENNReal.tsum_eq_zero.2 fun z => ?_
      split_ifs with hz
      · have : jumpc z y = 0 := by
          by_contra hne
          have := jump_supp_ge z y ((PMF.mem_support_iff _ _).2 hne)
          omega
        simp [this]
      · simp
  rw [h1]
  refine le_trans ?_ (ENNReal.tsum_le_tsum h2)
  rw [ENNReal.tsum_comm]
  apply le_of_eq
  unfold T
  refine tsum_congr fun z => ?_
  rw [ENNReal.tsum_mul_left, PMF.tsum_coe, mul_one]

lemma T_iter (j : ℕ) : ∀ m, 1 ≤ m → T 1 (m + j) ≤ T (1 + j) m := by
  induction j with
  | zero => intro m _; simp
  | succ j ih =>
    intro m hm
    calc T 1 (m + (j + 1)) = T 1 ((m + 1) + j) := by ring_nf
      _ ≤ T (1 + j) (m + 1) := ih (m + 1) (by omega)
      _ ≤ T (1 + j + 1) m := T_step _ _ hm
      _ = T (1 + (j + 1)) m := by ring_nf

lemma tsum_npr_top : ∑' k : ℕ, (k : ℝ≥0∞) * pmfN k = ⊤ := by
  by_contra hne
  apply not_summable_npr
  have heq : ∀ k : ℕ, (k : ℝ≥0∞) * pmfN k = ((Real.toNNReal ((k : ℝ) * pr k) : ℝ≥0∞)) := by
    intro k
    rw [pmfN_apply, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
    rfl
  simp_rw [heq] at hne
  have h2 := ENNReal.tsum_coe_ne_top_iff_summable.1 hne
  have h3 := NNReal.summable_coe.2 h2
  refine h3.congr fun n => ?_
  simp only [Real.coe_toNNReal _ (mul_nonneg (Nat.cast_nonneg n) (pr_nonneg n))]

lemma tail_sum : ∑' j : ℕ, (∑' k : ℕ, if 1 + j ≤ k then pmfN k else 0) = ⊤ := by
  rw [ENNReal.tsum_comm, ← tsum_npr_top]
  refine tsum_congr fun k => ?_
  rw [tsum_eq_sum (s := Finset.range k)]
  · rw [Finset.sum_congr rfl (g := fun _ => pmfN k)]
    · simp
    · intro j hj; simp at hj; rw [if_pos (by omega)]
  · intro j hj; simp at hj; rw [if_neg (by omega)]

lemma not_posrec : ¬ PositiveRecurrent jumpc := by
  intro h
  have h1 := (h x0).2
  unfold Stability.meanReturnTime at h1
  simp only [inv_one, ENNReal.ofReal_one, mul_one] at h1
  have key : ⊤ ≤ ∑' n : ℕ, ∑' y : Fin 1 → ℕ, Stability.tabooProb jumpc x0 n y := by
    have hsplit : ∀ F : ℕ → ℝ≥0∞, ∑' n, F n = F 0 + ∑' j, F (j + 1) :=
      fun F => tsum_eq_zero_add' ENNReal.summable
    rw [hsplit (fun n => ∑' y : Fin 1 → ℕ, Stability.tabooProb jumpc x0 n y)]
    refine le_trans ?_ le_add_self
    rw [← tail_sum]
    calc ∑' j : ℕ, (∑' k : ℕ, if 1 + j ≤ k then pmfN k else 0)
        = ∑' j : ℕ, T 1 (1 + j) := tsum_congr fun j => (T_one _ (by omega)).symm
      _ ≤ ∑' j : ℕ, T (1 + j) 1 := ENNReal.tsum_le_tsum fun j => T_iter j 1 le_rfl
      _ ≤ ∑' j : ℕ, ∑' y : Fin 1 → ℕ, Stability.tabooProb jumpc x0 (1 + j) y :=
          ENNReal.tsum_le_tsum fun j => ENNReal.tsum_le_tsum fun y => by
            unfold tab; split_ifs <;> simp
      _ = _ := by simp_rw [add_comm 1]
  exact absurd (lt_of_le_of_lt key h1) (lt_irrefl _)


lemma state_succ (z : Fin 1 → ℕ) (τ : ℕ) (ω : Ωc.{u}) :
    policyState datc Pc z (τ + 1) ω 0 = policyState datc Pc z τ ω 0 + (Pc.Eincr (τ + 1) ω 0 : ℤ)
      - ((if 1 ≤ (policyState datc Pc z τ ω 0).toNat then 1 else 0 : ℕ) : ℤ) := by
  rw [policyState, next_eq]; rfl

lemma Ecum_succ (τ : ℕ) (ω : Ωc.{u}) :
    Ecum Pc τ.succ ω 0 = Ecum Pc τ ω 0 + Pc.Eincr (τ + 1) ω 0 := by
  unfold Ecum; rw [Finset.sum_Icc_succ_top (by omega)]

lemma state_bounds (z : Fin 1 → ℕ) (ω : Ωc.{u}) (τ : ℕ) :
    0 ≤ policyState datc Pc z τ ω 0 ∧
    policyState datc Pc z τ ω 0 ≤ max ((z 0 : ℤ) - τ) 0 + (Ecum Pc τ ω 0 : ℤ) := by
  induction τ with
  | zero =>
    simp [policyState, Ecum]
  | succ τ ih =>
    rw [state_succ, Ecum_succ]
    obtain ⟨h1, h2⟩ := ih
    generalize policyState datc Pc z τ ω 0 = a at *
    generalize Pc.Eincr (τ + 1) ω 0 = e
    generalize Ecum Pc τ ω 0 = E at *
    rw [max_def] at h2 ⊢
    push_cast
    split_ifs at h2 ⊢ <;> omega

lemma fluid_stable : PacketFluidLimitStable datc Pc.{u} Sc (fun _ => 0) := by
  refine ⟨1, one_pos, ?_⟩
  rintro Dh Th Zh ⟨ω, zseq, hS, hsz, -, -, hZ⟩ t ht
  funext i; rw [Fin.fin_one_eq_zero i]
  by_contra hne
  have hc : 0 < |Zh t 0| := abs_pos.2 hne
  set ε := |Zh t 0| / 3 with hε
  have hε0 : 0 < ε := by positivity
  obtain ⟨N, hN⟩ := hZ t (by linarith) ε hε0
  obtain ⟨Nb, hNb⟩ := hS t (by linarith) ε hε0
  obtain ⟨n, hn1, hn2⟩ := ((hsz.eventually (eventually_ge_atTop (max Nb 1))).and
    (eventually_ge_atTop N)).exists
  have hs : sizeN (zseq n) = (zseq n 0 : ℝ) := by simp [sizeN]
  set s := sizeN (zseq n) with hsdef
  have hs1 : 1 ≤ s := le_trans (le_max_right _ _) hn1
  have hsNb : Nb ≤ s := le_trans (le_max_left _ _) hn1
  set τ := ⌊s * t⌋₊ with hτ
  have hzτ : zseq n 0 ≤ τ := by
    rw [hτ]; apply Nat.le_floor; rw [← hs]; nlinarith
  obtain ⟨b1, b2⟩ := state_bounds (zseq n) ω τ
  have hmax : max ((zseq n 0 : ℤ) - τ) 0 = 0 := by
    rw [max_eq_right]; omega
  rw [hmax, zero_add] at b2
  have hZn := hN n hn2 t ⟨by linarith, le_rfl⟩ 0
  have hEn := hNb s hsNb t ⟨by linarith, le_rfl⟩ 0
  simp only [zero_mul, sub_zero] at hEn
  replace hZn : |s⁻¹ * (policyState datc Pc (zseq n) τ ω 0 : ℝ) - Zh t 0| < ε := hZn
  replace hEn : |s⁻¹ * (Ecum Pc τ ω 0 : ℝ)| < ε := hEn
  have c1 : (0 : ℝ) ≤ (policyState datc Pc (zseq n) τ ω 0 : ℝ) := by exact_mod_cast b1
  have c2 : (policyState datc Pc (zseq n) τ ω 0 : ℝ) ≤ (Ecum Pc τ ω 0 : ℝ) := by exact_mod_cast b2
  have hsi : 0 < s⁻¹ := by positivity
  have d1 : 0 ≤ s⁻¹ * (policyState datc Pc (zseq n) τ ω 0 : ℝ) := by positivity
  have d2 : s⁻¹ * (policyState datc Pc (zseq n) τ ω 0 : ℝ) ≤ s⁻¹ * (Ecum Pc τ ω 0 : ℝ) :=
    mul_le_mul_of_nonneg_left c2 hsi.le
  have d3 := lt_of_le_of_lt (le_abs_self _) hEn
  have : |Zh t 0| < 2 * ε := by
    rw [abs_lt] at hZn ⊢; constructor <;> linarith
  linarith

end PNCex

theorem goal_disproof_core : ¬ (∀ {I J : ℕ} {Ω : Type} [MeasureSpace Ω]
    [IsProbabilityMeasure (ℙ : Measure Ω)]
    (dat : PacketNetworkData I J) (h121 : SatisfiesAssumption121 dat)
    (S : Finset (Fin J → ℕ)) (lam : Fin I → ℝ)
    (P : PacketPrimitives I J Ω) (hP : PrimitiveAssumptions P lam)
    (hadm : IsAdmissibleMarkovianPolicy dat S P.f)
    (jump : (Fin I → ℕ) → PMF (Fin I → ℕ)) (hjump : IsPolicyChain dat P jump)
    (hirr : Irreducible jump)
    (hstable : PacketFluidLimitStable dat P S lam),
    PositiveRecurrent jump) := by
  intro h
  exact PNCex.not_posrec (h PNCex.datc PNCex.h121c PNCex.Sc _ PNCex.Pc.{0} PNCex.PA.{0}
    PNCex.hadmc.{0} PNCex.jumpc PNCex.policyChain.{0} PNCex.irrc PNCex.fluid_stable.{0})

end ProcessingNetworks.PacketNetworks

open ProcessingNetworks.PacketNetworks


open MeasureTheory ProbabilityTheory

theorem solution : ¬ (∀ {I J : ℕ} {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    (dat : PacketNetworkData I J) (h121 : SatisfiesAssumption121 dat)
    (S : Finset (Fin J → ℕ)) (lam : Fin I → ℝ)
    (P : PacketPrimitives I J Ω) (hP : PrimitiveAssumptions P lam)
    (hadm : IsAdmissibleMarkovianPolicy dat S P.f)
    (jump : (Fin I → ℕ) → PMF (Fin I → ℕ)) (hjump : IsPolicyChain dat P jump)
    (hirr : Irreducible jump)
    (hstable : PacketFluidLimitStable dat P S lam),
    PositiveRecurrent jump) :=
  goal_disproof_core
