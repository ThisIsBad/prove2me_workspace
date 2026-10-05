import Mathlib
import Definitions.Def_ProcessingNetworks_PacketNetworks_RPSFluidModel
import Definitions.Def_ProcessingNetworks_PacketNetworks_BPAmbientChain

namespace ProcessingNetworks.PacketNetworks

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace BPSCE

noncomputable def unif : Measure ℝ := volume.restrict (Set.Ioo (0 : ℝ) 1)

instance : IsProbabilityMeasure unif := ⟨by simp [unif, Real.volume_Ioo]⟩

noncomputable def gN (x : ℝ) : ℕ := ⌊x⁻¹⌋₊ - 1

theorem gN_meas : Measurable gN := by
  unfold gN
  exact (measurable_of_countable (fun n : ℕ => n - 1)).comp (Nat.measurable_floor.comp (measurable_inv (G := ℝ)))

abbrev Ωc : Type := ℕ ⊕ ℕ → ℝ

noncomputable instance : MeasureSpace Ωc := ⟨Measure.infinitePi (fun _ : ℕ ⊕ ℕ => unif)⟩

theorem vol_eq : (ℙ : Measure Ωc) = Measure.infinitePi (fun _ : ℕ ⊕ ℕ => unif) := rfl

instance : IsProbabilityMeasure (ℙ : Measure Ωc) := by
  rw [vol_eq]; infer_instance

noncomputable def gv (x : ℝ) : Fin 1 → ℕ := fun _ => gN x

theorem gv_meas : Measurable gv := measurable_pi_lambda _ (fun _ => gN_meas)

noncomputable def Pc : PacketPrimitives 1 1 Ωc where
  f z _ := if 1 ≤ z 0 then fun _ => 1 else fun _ => 0
  Eincr τ ω := gv ((ω : ℕ ⊕ ℕ → ℝ) (Sum.inl τ))
  U τ ω := (ω : ℕ ⊕ ℕ → ℝ) (Sum.inr τ)

theorem ev_meas (i : ℕ ⊕ ℕ) : Measurable (fun ω : Ωc => (ω : ℕ ⊕ ℕ → ℝ) i) :=
  measurable_pi_apply i

theorem map_ev (i : ℕ ⊕ ℕ) : (ℙ : Measure Ωc).map (fun ω : Ωc => (ω : ℕ ⊕ ℕ → ℝ) i) = unif := by
  rw [vol_eq]; exact Measure.infinitePi_map_eval _ i

theorem indep_all : iIndepFun (fun (i : ℕ ⊕ ℕ) (ω : Ωc) => (ω : ℕ ⊕ ℕ → ℝ) i) ℙ := by
  rw [vol_eq]
  exact iIndepFun_infinitePi (X := fun _ x => x) (fun _ => measurable_id)

theorem prob_E1 (A : Set (Fin 1 → ℕ)) :
    (ℙ : Measure Ωc) {ω | Pc.Eincr 1 ω ∈ A} = unif (gv ⁻¹' A) := by
  rw [← map_ev (Sum.inl 1), Measure.map_apply (ev_meas _) (gv_meas (Set.to_countable A).measurableSet)]
  rfl

theorem not_int : ¬ Integrable (fun x => ((gN x : ℕ) : ℝ)) unif := by
  intro h
  have h2 : IntegrableOn (fun x : ℝ => ((gN x : ℕ) : ℝ) + 2) (Set.Ioo (0:ℝ) 1) := by
    exact (h.add (integrable_const 2))
  have h3 : IntegrableOn (fun x : ℝ => x⁻¹) (Set.Ioo (0:ℝ) 1) := by
    refine h2.mono' (by fun_prop) ?_
    refine (ae_restrict_iff' measurableSet_Ioo).mpr (Filter.Eventually.of_forall ?_)
    intro x hx
    have hxpos : 0 < x⁻¹ := inv_pos.mpr hx.1
    rw [Real.norm_eq_abs, abs_of_pos hxpos]
    have := Nat.lt_floor_add_one x⁻¹
    unfold gN
    have : ((⌊x⁻¹⌋₊ - 1 : ℕ) : ℝ) ≥ (⌊x⁻¹⌋₊ : ℝ) - 1 := by
      rcases Nat.eq_zero_or_pos ⌊x⁻¹⌋₊ with h0 | h0
      · rw [h0]; simp
      · rw [Nat.cast_sub h0]; simp
    linarith
  have h4 : IntervalIntegrable (fun x : ℝ => x⁻¹) volume 0 1 := by
    rw [intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one]; exact h3
  rw [intervalIntegrable_inv_iff] at h4
  simp at h4

theorem prim : PrimitiveAssumptions Pc (fun _ => 0) where
  arrivals_indep := by
    have := (indep_all.precomp (g := fun τ : ℕ => Sum.inl (τ + 1))
      (fun a b h => by simpa using h)).comp (fun _ => gv) (fun _ => gv_meas)
    exact this
  arrivals_ident := by
    intro τ
    have h : IdentDistrib (fun ω : Ωc => (ω : ℕ ⊕ ℕ → ℝ) (Sum.inl (τ + 1)))
        (fun ω : Ωc => (ω : ℕ ⊕ ℕ → ℝ) (Sum.inl 1)) ℙ ℙ :=
      ⟨(ev_meas _).aemeasurable, (ev_meas _).aemeasurable, by rw [map_ev, map_ev]⟩
    exact h.comp gv_meas
  classes_indep := iIndepFun.of_subsingleton
  arrival_mean := by
    intro i
    rw [integral_undef]
    intro hint
    apply not_int
    have : Integrable (fun x => ((gN x : ℕ) : ℝ)) ((ℙ : Measure Ωc).map
        (fun ω : Ωc => (ω : ℕ ⊕ ℕ → ℝ) (Sum.inl 1))) := by
      exact (integrable_map_measure ((measurable_of_countable (fun n : ℕ => (n:ℝ))).comp gN_meas).aestronglyMeasurable (ev_meas _).aemeasurable).mpr hint
    rwa [map_ev] at this
  arrival_zero := by
    have := prob_E1 {0}
    simp only [Set.mem_singleton_iff] at this
    rw [this]
    have hsub : Set.Ioo (1/2 : ℝ) 1 ⊆ gv ⁻¹' {0} ∩ Set.Ioo 0 1 := by
      intro x hx
      refine ⟨?_, ⟨by linarith [hx.1], hx.2⟩⟩
      simp only [Set.mem_preimage, Set.mem_singleton_iff]
      funext k
      simp only [gv, gN, Pi.zero_apply]
      have hx0 : 0 < x := by linarith [hx.1]
      have : x⁻¹ < 2 := by
        rw [inv_lt_comm₀ hx0 (by norm_num)]; linarith [hx.1]
      have : ⌊x⁻¹⌋₊ < 2 := (Nat.floor_lt (by positivity)).mpr (by exact_mod_cast this)
      omega
    have := measure_mono (μ := volume) hsub
    unfold unif
    rw [Measure.restrict_apply (gv_meas (Set.to_countable _).measurableSet)]
    refine lt_of_lt_of_le ?_ this
    simp [Real.volume_Ioo]
    norm_num
  uniform := by
    intro τ
    exact map_ev (Sum.inr (τ + 1))
  uniform_indep := by
    exact indep_all.precomp (g := fun τ : ℕ => Sum.inr (τ + 1)) (fun a b h => by simpa using h)
  arrivals_uniform_indep := by
    have hI := (iIndepFun_iff_iIndep _ _ _).mp indep_all
    have hle : ∀ i, MeasurableSpace.comap (fun ω : Ωc => (ω : ℕ ⊕ ℕ → ℝ) i) inferInstance ≤
        (inferInstance : MeasurableSpace Ωc) := fun i => (ev_meas i).comap_le
    have hd := indep_iSup_of_disjoint hle hI
      (S := Set.range Sum.inl) (T := Set.range Sum.inr) (by
        rw [Set.disjoint_left]; rintro _ ⟨a, rfl⟩ ⟨b, hb⟩; cases hb)
    refine indep_of_indep_of_le_right (indep_of_indep_of_le_left hd ?_) ?_
    · refine iSup_le fun τ => ?_
      refine le_trans ?_ (le_iSup₂ (f := fun i (_ : i ∈ Set.range Sum.inl) =>
        MeasurableSpace.comap (fun ω : Ωc => (ω : ℕ ⊕ ℕ → ℝ) i) inferInstance)
        (Sum.inl (τ + 1)) ⟨_, rfl⟩)
      show MeasurableSpace.comap (gv ∘ fun ω : Ωc => (ω : ℕ ⊕ ℕ → ℝ) (Sum.inl (τ + 1))) _ ≤ _
      rw [← MeasurableSpace.comap_comp]
      exact MeasurableSpace.comap_mono gv_meas.comap_le
    · refine iSup_le fun τ => ?_
      exact le_iSup₂ (f := fun i (_ : i ∈ Set.range Sum.inr) =>
        MeasurableSpace.comap (fun ω : Ωc => (ω : ℕ ⊕ ℕ → ℝ) i) inferInstance)
        (Sum.inr (τ + 1)) ⟨_, rfl⟩
  policy_measurable := fun _ => measurable_const

def datc : PacketNetworkData 1 1 := ⟨fun _ => 0, fun _ => none⟩

theorem h121c : SatisfiesAssumption121 datc := by
  refine ⟨fun i => ⟨0, Subsingleton.elim _ _⟩, fun n js h => ?_⟩
  have := h 0
  simp [datc] at this

noncomputable def cfgc : LinkConfigData 1 1 where
  A := fun _ _ => 1
  hA := fun j => ⟨0, rfl, fun k _ => Subsingleton.elim _ _⟩
  hA0 := fun j k h => absurd rfl h
  C := {fun _ => 1}

theorem h124c : SatisfiesAssumption124 cfgc := fun k => ⟨fun _ => 1, by simp [cfgc], by norm_num⟩

def Sc : Finset (Fin 1 → ℕ) := {fun _ => 0, fun _ => 1}

theorem fin1_eq (s t : Fin 1 → ℕ) : s = t ↔ s 0 = t 0 := by
  constructor
  · intro h; rw [h]
  · intro h; funext i; rw [Subsingleton.elim i 0]; exact h

theorem hSc : IsScheduleSet cfgc Sc := by
  intro s
  simp only [Sc, Finset.mem_insert, Finset.mem_singleton, fin1_eq, cfgc, scheduleAvailable]
  simp [Matrix.mulVec, dotProduct]
  constructor
  · intro h; exact ⟨fun _ => 1, rfl, by show s 0 ≤ 1; omega⟩
  · rintro ⟨c, hc, h⟩; omega

theorem R_c : ∀ (v : Fin 1 → ℝ), (R datc).mulVec v 0 = v 0 := by
  intro v; simp [R, datc, Matrix.mulVec, dotProduct]

theorem E1_meas : Measurable (Pc.Eincr 1) := gv_meas.comp (ev_meas _)

instance : IsProbabilityMeasure ((ℙ : Measure Ωc).map (Pc.Eincr 1)) :=
  Measure.isProbabilityMeasure_map E1_meas.aemeasurable

noncomputable def qc : PMF (Fin 1 → ℕ) := ((ℙ : Measure Ωc).map (Pc.Eincr 1)).toPMF



theorem qc_apply (e : Fin 1 → ℕ) : qc e = ℙ {ω : Ωc | Pc.Eincr 1 ω = e} := by
  rw [qc, Measure.toPMF_apply, Measure.map_apply E1_meas (measurableSet_singleton e)]
  rfl

def nxt (z e : Fin 1 → ℕ) : Fin 1 → ℕ := fun _ => z 0 - 1 + e 0

noncomputable def jumpc (z : Fin 1 → ℕ) : PMF (Fin 1 → ℕ) := qc.map (nxt z)

theorem chain_c : IsPolicyChain datc Pc jumpc := by
  intro z y
  have hconst : ∀ u : ℝ, (∑' e : Fin 1 → ℕ,
      (if (fun i => (y i : ℤ)) = nextState datc (fun i => (z i : ℤ)) e (Pc.f z u) then
        ℙ {ω : Ωc | Pc.Eincr 1 ω = e} else 0)) = jumpc z y := by
    intro u
    rw [jumpc, PMF.map_apply]
    apply tsum_congr
    intro e
    rw [qc_apply]
    congr 1
    apply propext
    rw [fin1_eq]
    have hns : ∀ i, nextState datc (fun i => (z i : ℤ)) e (Pc.f z u) i =
        (z 0 : ℤ) + e 0 - (if 1 ≤ z 0 then 1 else 0) := by
      intro i
      rw [Subsingleton.elim i 0]
      simp only [nextState, Rint, datc, Pc]
      split_ifs <;> simp_all
    constructor
    · intro h
      have := congrFun h 0
      rw [hns] at this
      simp only [nxt]
      split_ifs at this with hz <;> omega
    · intro h
      funext i
      rw [Subsingleton.elim i 0, hns]
      simp only [nxt] at h
      split_ifs with hz <;> omega
  simp_rw [hconst]
  rw [setLIntegral_const, Real.volume_Ioo]
  simp

theorem jump0 : jumpc 0 = qc := by
  have : nxt 0 = id := by
    funext e; rw [fin1_eq]; simp [nxt]
  rw [jumpc, this, PMF.map_id]

theorem jump_supp (z y : Fin 1 → ℕ) (k : ℕ) (hz : k + 1 ≤ z 0) (h : jumpc z y ≠ 0) : k ≤ y 0 := by
  have : y ∈ (jumpc z).support := (PMF.mem_support_iff _ _).mpr h
  rw [jumpc, PMF.mem_support_map_iff] at this
  obtain ⟨e, -, rfl⟩ := this
  simp only [nxt]; omega

theorem G_bound (m : ℕ) :
    ENNReal.ofReal (1 / (m + 1)) ≤ ∑' y : Fin 1 → ℕ, (if m ≤ y 0 then qc y else 0) := by
  have hA : MeasurableSet {y : Fin 1 → ℕ | m ≤ y 0} := (Set.to_countable _).measurableSet
  have h1 : (∑' y : Fin 1 → ℕ, (if m ≤ y 0 then qc y else 0)) =
      qc.toMeasure {y : Fin 1 → ℕ | m ≤ y 0} := by
    rw [PMF.toMeasure_apply _ hA]
    apply tsum_congr; intro y
    simp [Set.indicator]
  rw [h1, qc, Measure.toPMF_toMeasure, Measure.map_apply E1_meas hA]
  have h2 := prob_E1 {y : Fin 1 → ℕ | m ≤ y 0}
  rw [show Pc.Eincr 1 ⁻¹' {y : Fin 1 → ℕ | m ≤ y 0} = {ω | Pc.Eincr 1 ω ∈ {y : Fin 1 → ℕ | m ≤ y 0}}
    from rfl, h2]
  unfold unif
  rw [Measure.restrict_apply (gv_meas hA)]
  have hsub : Set.Ioo (0 : ℝ) (1 / (m + 1)) ⊆ gv ⁻¹' {y : Fin 1 → ℕ | m ≤ y 0} ∩ Set.Ioo 0 1 := by
    intro x hx
    have hm1 : (1 : ℝ) / (m + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]; have : (0:ℝ) ≤ m := by positivity
      linarith
    refine ⟨?_, hx.1, lt_of_lt_of_le hx.2 hm1⟩
    simp only [Set.mem_preimage, Set.mem_setOf_eq, gv, gN]
    have hx0 := hx.1
    have : (m + 1 : ℝ) < x⁻¹ := by
      have := hx.2
      rw [lt_inv_comm₀ (by positivity) hx0]; simpa using this
    have : m + 1 ≤ ⌊x⁻¹⌋₊ := Nat.le_floor (by push_cast; linarith)
    omega
  refine le_trans (le_of_eq ?_) (measure_mono hsub)
  rw [Real.volume_Ioo]; simp

open Classical in
theorem taboo_bound (n : ℕ) : ∀ k : ℕ, 1 ≤ k →
    (∑' y : Fin 1 → ℕ, (if n + k ≤ y 0 then qc y else 0)) ≤
      ∑' y : Fin 1 → ℕ, (if k ≤ y 0 then Stability.tabooProb jumpc 0 (n + 1) y else 0) := by
  induction n with
  | zero =>
    intro k hk
    apply ENNReal.tsum_le_tsum
    intro y
    split_ifs with h1 h2
    · have hy : y ≠ 0 := by intro h; rw [h] at h2; simp at h2; omega
      simp only [Stability.tabooProb, if_neg hy]
      rw [← jump0]
      rw [tsum_eq_single (0 : Fin 1 → ℕ)]
      · simp
      · intro b hb; simp [hb]
    · simp at h1; omega
    · exact zero_le
    · exact le_rfl
  | succ n ih =>
    intro k hk
    refine le_trans (by rw [show n + 1 + k = n + (k + 1) by ring]) (ih (k + 1) (by omega)) |>.trans ?_
    -- ∑ [k+1 ≤ z0] taboo (n+1) z ≤ ∑ [k ≤ y0] taboo (n+2) y
    have key : ∀ y : Fin 1 → ℕ,
        (∑' z : Fin 1 → ℕ, (if k + 1 ≤ z 0 then Stability.tabooProb jumpc 0 (n + 1) z else 0)
          * jumpc z y) ≤
        (if k ≤ y 0 then Stability.tabooProb jumpc 0 (n + 1 + 1) y else 0) := by
      intro y
      by_cases hy : k ≤ y 0
      · have hy0 : y ≠ 0 := by intro h; rw [h] at hy; simp at hy; omega
        rw [if_pos hy]
        conv_rhs => rw [Stability.tabooProb, if_neg hy0]
        apply ENNReal.tsum_le_tsum
        intro z
        split_ifs <;> simp
      · rw [if_neg hy]
        apply le_of_eq
        apply ENNReal.tsum_eq_zero.mpr
        intro z
        split_ifs with hz
        · have : jumpc z y = 0 := by
            by_contra hne; exact hy (jump_supp z y k hz hne)
          simp [this]
        · simp
    refine le_trans (le_of_eq ?_) (ENNReal.tsum_le_tsum key)
    rw [ENNReal.tsum_comm]
    apply tsum_congr
    intro z
    rw [ENNReal.tsum_mul_left, PMF.tsum_coe, mul_one]

theorem harmonic_top : (∑' n : ℕ, ENNReal.ofReal (1 / ((n + 1 : ℕ) + 1 : ℝ))) = ⊤ := by
  by_contra h
  have hs := ENNReal.summable_toReal h
  have hs2 : Summable (fun n : ℕ => 1 / ((n + 2 : ℕ) : ℝ)) := by
    refine hs.congr (fun n => ?_)
    rw [ENNReal.toReal_ofReal (by positivity)]
    push_cast; ring_nf
  have : Summable (fun n : ℕ => 1 / (n : ℝ)) :=
    (summable_nat_add_iff 2).mp hs2
  exact Real.not_summable_one_div_natCast this

theorem mrt_top : Stability.meanReturnTime jumpc (fun _ => (1 : ℝ)) 0 = ⊤ := by
  unfold Stability.meanReturnTime
  simp only [inv_one, ENNReal.ofReal_one, mul_one]
  refine top_le_iff.mp (le_trans (le_of_eq harmonic_top.symm) ?_)
  refine le_trans ?_ (ENNReal.tsum_comp_le_tsum_of_injective (f := fun n : ℕ => n + 1)
    (fun a b h => by simpa using h) _)
  apply ENNReal.tsum_le_tsum
  intro n
  have h1 := G_bound (n + 1)
  have h2 := taboo_bound n 1 le_rfl
  refine le_trans (by simpa using h1) (le_trans h2 ?_)
  apply ENNReal.tsum_le_tsum
  intro y
  split_ifs <;> simp


/-! ## RPS instance -/

noncomputable def cfg2 : LinkConfigData 1 1 where
  A := fun _ _ => 1
  hA := fun j => ⟨0, rfl, fun k _ => Subsingleton.elim _ _⟩
  hA0 := fun j k h => absurd rfl h
  C := {fun _ => 0, fun _ => 1}

theorem h124_2 : SatisfiesAssumption124 cfg2 := fun k => ⟨fun _ => 1, by simp [cfg2], by norm_num⟩

theorem hS2 : IsScheduleSet cfg2 Sc := by
  intro s
  simp only [Sc, Finset.mem_insert, Finset.mem_singleton, fin1_eq, cfg2, scheduleAvailable]
  simp [Matrix.mulVec, dotProduct]
  constructor
  · intro h; exact ⟨fun _ => 1, Or.inr rfl, by show s 0 ≤ 1; omega⟩
  · rintro ⟨c, hc, h⟩
    rcases hc with hc | hc <;> omega

noncomputable def fr2 : FixedRoutingData 1 1 where
  dat := datc
  u_id := by funext i; exact Subsingleton.elim _ _
  cfg := cfg2
  linkDesig := fun _ => 0
  A_desig := fun k i => by simp [cfg2, Subsingleton.elim k 0]

theorem hull2 : hullFinset fr2.cfg.C = Set.Icc (0 : Fin 1 → ℝ) 1 := by
  apply le_antisymm
  · apply convexHull_min _ (convex_Icc _ _)
    rintro x ⟨c, hc, rfl⟩
    simp only [fr2, cfg2, Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hc
    rcases hc with rfl | rfl
    · constructor <;> intro i <;> simp [realize]
    · constructor <;> intro i <;> simp [realize]
  · intro x hx
    have h0 : realize (fun _ : Fin 1 => (0:ℕ)) ∈ hullFinset fr2.cfg.C :=
      subset_convexHull ℝ _ ⟨fun _ => 0, by simp [fr2, cfg2], rfl⟩
    have h1 : realize (fun _ : Fin 1 => (1:ℕ)) ∈ hullFinset fr2.cfg.C :=
      subset_convexHull ℝ _ ⟨fun _ => 1, by simp [fr2, cfg2], rfl⟩
    have ha : 0 ≤ x 0 := hx.1 0
    have hb : x 0 ≤ 1 := hx.2 0
    have := (convex_convexHull ℝ _) h1 h0 ha (by linarith : 0 ≤ 1 - x 0) (by ring)
    have hx' : x = (x 0 • realize fun _ : Fin 1 => (1:ℕ)) + (1 - x 0) • realize fun _ : Fin 1 => (0:ℕ) := by
      ext i; fin_cases i; simp [realize]
    rw [hx']; exact this

theorem hdom2 : ProportionalFairness.IsPFDomain (hullFinset fr2.cfg.C) := by
  rw [hull2]
  refine ⟨Metric.isBounded_Icc _ _, isClosed_Icc, convex_Icc _ _, ?_, ?_⟩
  · intro x hx y hy hyx
    exact ⟨fun i => hy i, le_trans hyx hx.2⟩
  · exact ⟨1, ⟨fun i => by simp, fun i => le_rfl⟩, fun i => by simp⟩

theorem one_mem_hull2 : (fun _ => (1:ℝ)) ∈ hullFinset fr2.cfg.C := by
  rw [hull2]; exact ⟨fun i => by simp, fun i => le_rfl⟩

theorem pfmax2 (y : Fin 1 → ℝ) (hy : ∀ i, 0 ≤ y i) :
    ProportionalFairness.IsPFMaximizer (hullFinset fr2.cfg.C) y (fun _ => 1) := by
  refine ⟨one_mem_hull2, fun x hx => ?_⟩
  rw [hull2] at hx
  simp only [ProportionalFairness.f, ProportionalFairness.extLog, one_ne_zero, if_false,
    Real.log_one, EReal.coe_zero, mul_zero, Finset.sum_const_zero]
  apply Finset.sum_nonpos
  intro i _
  have hx1 : x i ≤ 1 := hx.2 i
  have hx0 : 0 ≤ x i := hx.1 i
  have hyi : (0 : EReal) ≤ (y i : EReal) := by exact_mod_cast hy i
  split_ifs with h
  · rcases hyi.lt_or_eq with h' | h'
    · rw [EReal.mul_bot_of_pos h']; exact bot_le
    · rw [← h']; simp
  · have : (Real.log (x i) : EReal) ≤ 0 := by exact_mod_cast Real.log_nonpos hx0 hx1
    exact EReal.mul_nonpos_iff.mpr (Or.inl ⟨hyi, this⟩)

theorem hRPS2 : IsRPSPolicy fr2 Sc Pc.f := by
  refine ⟨?_, fun _ _ => fun _ => 1, fun _ => measurable_const, ?_, ?_, ?_⟩
  · intro z u _ _
    refine ⟨?_, fun i => ?_⟩
    · simp only [Pc, Sc]; split_ifs <;> simp
    · rw [Subsingleton.elim i 0]
      simp only [B, fr2, datc, Pc, Matrix.mulVec, dotProduct]
      by_cases h : 1 ≤ z 0
      · simp [h]
      · simp [h]
  · intro y uu _ _; simp [fr2, cfg2]
  · intro y
    refine ⟨fun _ => 1, pfmax2 _ (fun _ => by positivity), fun k => ?_⟩
    simp [Real.volume_Ioo]
  · intro z c hc s
    have hlc : linkClasses fr2 0 = {0} := by
      ext i; simp [linkClasses, fr2, Subsingleton.elim i 0]
    have hsp : selectionProb fr2 z c s =
        if s 0 = min (c 0) (z 0) then
          ((z 0).choose (s 0) : ℝ) / ((z 0).choose (min (c 0) (z 0)) : ℝ) else 0 := by
      simp [selectionProb, linkCounts, hlc, Fin.prod_univ_one]
    simp only [fr2, cfg2, Finset.mem_insert, Finset.mem_singleton] at hc
    rcases hc with rfl | rfl
    · have : ¬ ((fun _ : Fin 1 => (1:ℕ)) = fun _ => 0) := by
        intro h; have := congrFun h 0; simp at this
      simp [this]
    · simp only [true_and, and_true]
      have hV : (volume {uu : ℝ | uu ∈ Set.Ioo (0:ℝ) 1}) = 1 := by
        show volume (Set.Ioo (0:ℝ) 1) = 1
        simp [Real.volume_Ioo]
      rw [hV, one_mul, hsp]
      by_cases hz : 1 ≤ z 0
      · have hm : min 1 (z 0) = 1 := min_eq_left hz
        rw [hm]
        by_cases hs : s 0 = 1
        · have hs' : s = fun _ => 1 := by funext i; rw [Subsingleton.elim i 0, hs]
          subst hs'
          have : ((z 0 : ℕ) : ℝ) ≠ 0 := by
            have : 0 < z 0 := by omega
            exact_mod_cast this.ne'
          simp [Pc, hz, this]
          show volume (Set.Ioo (0:ℝ) 1) = 1
          simp [Real.volume_Ioo]
        · have : ∀ uu, Pc.f z uu ≠ s := by
            intro uu h; apply hs; rw [← h]; simp [Pc, hz]
          simp [this, hs]
      · have hz0 : z 0 = 0 := by omega
        have hm : min 1 (z 0) = 0 := by rw [hz0]; rfl
        rw [hm]
        by_cases hs : s 0 = 0
        · have hs' : s = fun _ => 0 := by funext i; rw [Subsingleton.elim i 0, hs]
          subst hs'
          have hf : ∀ uu, Pc.f z uu = fun _ => 0 := by intro uu; simp [Pc, hz]
          simp [hf]
          show volume (Set.Ioo (0:ℝ) 1) = 1
          simp [Real.volume_Ioo]
        · have : ∀ uu, Pc.f z uu ≠ s := by
            intro uu h; apply hs; rw [← h]; simp [Pc, hz]
          simp [this, hs]

theorem halpha2 : ProportionalFairness.IsTotalArrivalRates (toPFData fr2 (fun _ => 0)) (fun _ => 0) := by
  funext i; simp [toPFData]

theorem hload2 : ∃ chat ∈ hullFinset fr2.cfg.C,
    ∀ k, ProportionalFairness.groupAggregate fr2.linkDesig (fun _ => (0:ℝ)) k < chat k :=
  ⟨fun _ => 1, one_mem_hull2, fun k => by simp [ProportionalFairness.groupAggregate]⟩

theorem not_posrec : ¬ PositiveRecurrentOn jumpc (reachableFrom jumpc 0) := by
  intro key
  have h0 : (0 : Fin 1 → ℕ) ∈ reachableFrom jumpc 0 := ⟨0, by
    show 0 < (PMF.pure (0 : Fin 1 → ℕ)) 0
    simp⟩
  have := (key 0 h0).2
  rw [mrt_top] at this
  exact lt_irrefl _ this

end BPSCE

theorem rps_goal_false : ¬ (∀ {I K : ℕ} {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    (fr : FixedRoutingData I K) (h121 : SatisfiesAssumption121 fr.dat)
    (h124 : SatisfiesAssumption124 fr.cfg)
    (hdom : ProportionalFairness.IsPFDomain (hullFinset fr.cfg.C))
    (S : Finset (Fin I → ℕ)) (hS : IsScheduleSet fr.cfg S)
    (lam : Fin I → ℝ) (P : PacketPrimitives I I Ω) (hP : PrimitiveAssumptions P lam)
    (hRPS : IsRPSPolicy fr S P.f)
    (jump : (Fin I → ℕ) → PMF (Fin I → ℕ)) (hjump : IsPolicyChain fr.dat P jump)
    (alpha : Fin I → ℝ) (halpha : ProportionalFairness.IsTotalArrivalRates (toPFData fr lam) alpha)
    (hload : ∃ chat ∈ hullFinset fr.cfg.C,
      ∀ k, ProportionalFairness.groupAggregate fr.linkDesig alpha k < chat k),
    RPSFluidStable fr S lam ∧ PositiveRecurrentOn jump (reachableFrom jump 0)) := by
  intro h
  exact BPSCE.not_posrec (h BPSCE.fr2 BPSCE.h121c BPSCE.h124_2 BPSCE.hdom2 BPSCE.Sc BPSCE.hS2
    _ BPSCE.Pc BPSCE.prim BPSCE.hRPS2 BPSCE.jumpc BPSCE.chain_c _ BPSCE.halpha2 BPSCE.hload2).2

end ProcessingNetworks.PacketNetworks

open ProcessingNetworks ProcessingNetworks.PacketNetworks MeasureTheory ProbabilityTheory

theorem solution : ¬ (∀ {I K : ℕ} {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    (fr : FixedRoutingData I K) (h121 : SatisfiesAssumption121 fr.dat)
    (h124 : SatisfiesAssumption124 fr.cfg)
    (hdom : ProportionalFairness.IsPFDomain (hullFinset fr.cfg.C))
    (S : Finset (Fin I → ℕ)) (hS : IsScheduleSet fr.cfg S)
    (lam : Fin I → ℝ) (P : PacketPrimitives I I Ω) (hP : PrimitiveAssumptions P lam)
    (hRPS : IsRPSPolicy fr S P.f)
    (jump : (Fin I → ℕ) → PMF (Fin I → ℕ)) (hjump : IsPolicyChain fr.dat P jump)
    (alpha : Fin I → ℝ) (halpha : ProportionalFairness.IsTotalArrivalRates (toPFData fr lam) alpha)
    (hload : ∃ chat ∈ hullFinset fr.cfg.C,
      ∀ k, ProportionalFairness.groupAggregate fr.linkDesig alpha k < chat k),
    RPSFluidStable fr S lam ∧ PositiveRecurrentOn jump (reachableFrom jump 0)) :=
  ProcessingNetworks.PacketNetworks.rps_goal_false
