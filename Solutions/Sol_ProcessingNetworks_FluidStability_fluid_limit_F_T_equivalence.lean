import Mathlib
import Definitions.Def_ProcessingNetworks_Stability_MarkovRepresentation
import Definitions.Def_ProcessingNetworks_FluidStability_FluidEquationData
import Definitions.Def_ProcessingNetworks_Stability_SPNModel
import Definitions.Def_ProcessingNetworks_FluidStability_SPNProcessFamily

namespace ProcessingNetworks.FluidStability

open MeasureTheory ProbabilityTheory Filter ProcessingNetworks.Stability Topology
open scoped ENNReal

namespace FTCex

open Classical

noncomputable def μU : Measure ℝ := volume.restrict (Set.Ioo (0:ℝ) 1)

instance : IsProbabilityMeasure μU := ⟨by simp [μU, Real.volume_Ioo]⟩

noncomputable def μB : Measure Bool := (PMF.uniformOfFintype Bool).toMeasure

instance : IsProbabilityMeasure μB := by unfold μB; infer_instance

abbrev Ωc : Type := (ℕ → ℝ) × Bool

noncomputable instance msΩ : MeasureSpace Ωc :=
  ⟨(Measure.infinitePi (fun _ : ℕ => μU)).prod μB⟩

lemma vol_eq : (ℙ : Measure Ωc) = (Measure.infinitePi (fun _ : ℕ => μU)).prod μB := rfl

instance : IsProbabilityMeasure (ℙ : Measure Ωc) := by
  rw [vol_eq]; infer_instance

lemma map_fst : (ℙ : Measure Ωc).map Prod.fst = Measure.infinitePi (fun _ : ℕ => μU) := by
  rw [vol_eq, Measure.map_fst_prod, measure_univ, one_smul]

lemma indep_cross : Indep (MeasurableSpace.comap (Prod.fst : Ωc → _) inferInstance)
    (MeasurableSpace.comap (Prod.snd : Ωc → _) inferInstance) ℙ := by
  have := indepFun_prod (μ := Measure.infinitePi (fun _ : ℕ => μU))
    (ν := μB) (X := id) (Y := id) measurable_id measurable_id
  rw [IndepFun_iff_Indep] at this
  exact this

/-- the "good" sequences of uniforms -/
def G : Set (ℕ → ℝ) :=
  {u | (∀ n, u n ∈ Set.Ioo (0:ℝ) 1) ∧ ∀ M : ℕ, ∃ n, (M : ℝ) ≤ ∑ k ∈ Finset.range n, -Real.log (u k)}

lemma G_meas : MeasurableSet G := by
  have h1 : MeasurableSet {u : ℕ → ℝ | ∀ n, u n ∈ Set.Ioo (0:ℝ) 1} := by
    simp only [Set.setOf_forall]
    exact MeasurableSet.iInter fun n => measurableSet_Ioo.preimage (measurable_pi_apply n)
  have h2 : MeasurableSet {u : ℕ → ℝ | ∀ M : ℕ, ∃ n, (M : ℝ) ≤
      ∑ k ∈ Finset.range n, -Real.log (u k)} := by
    simp only [Set.setOf_forall, Set.setOf_exists]
    refine MeasurableSet.iInter fun M => MeasurableSet.iUnion fun n => ?_
    exact measurableSet_le measurable_const
      (Finset.measurable_sum _ fun k _ => ((measurable_pi_apply k).log).neg)
  exact h1.inter h2

lemma ioo_ae : ∀ᵐ u ∂(Measure.infinitePi (fun _ : ℕ => μU)), ∀ n, u n ∈ Set.Ioo (0:ℝ) 1 := by
  rw [ae_all_iff]
  intro n
  have h : (Measure.infinitePi (fun _ : ℕ => μU)).map (fun u => u n) = μU :=
    Measure.infinitePi_map_eval _ n
  have : ∀ᵐ y ∂μU, y ∈ Set.Ioo (0:ℝ) 1 := by
    unfold μU; exact ae_restrict_mem measurableSet_Ioo
  rw [← h] at this
  exact ae_of_ae_map (measurable_pi_apply n).aemeasurable this

lemma bc_ae : ∀ᵐ u ∂(Measure.infinitePi (fun _ : ℕ => μU)),
    ∃ᶠ n in atTop, u ∈ {u : ℕ → ℝ | u n < Real.exp (-1)} := by
  set s : ℕ → Set (ℕ → ℝ) := fun n => {u | u n < Real.exp (-1)} with hs
  have hsm : ∀ n, MeasurableSet (s n) := fun n =>
    measurableSet_Iio.preimage (measurable_pi_apply n)
  have hind : iIndepSet s (Measure.infinitePi (fun _ : ℕ => μU)) := by
    rw [iIndepSet_iff_iIndep]
    have h0 := iIndepFun_infinitePi (P := fun _ : ℕ => μU) (X := fun _ => (id : ℝ → ℝ))
      (fun _ => measurable_id)
    rw [iIndepFun_iff_iIndep] at h0
    refine iIndep_of_iIndep_of_le h0 (fun n => ?_)
    refine MeasurableSpace.generateFrom_le ?_
    intro t ht
    rw [Set.mem_singleton_iff] at ht
    subst ht
    exact ⟨Set.Iio (Real.exp (-1)), measurableSet_Iio, rfl⟩
  have hmeas : ∀ n, (Measure.infinitePi (fun _ : ℕ => μU)) (s n) = ENNReal.ofReal (Real.exp (-1)) := by
    intro n
    have h : (Measure.infinitePi (fun _ : ℕ => μU)).map (fun u => u n) = μU :=
      Measure.infinitePi_map_eval _ n
    have : (Measure.infinitePi (fun _ : ℕ => μU)) (s n) =
        ((Measure.infinitePi (fun _ : ℕ => μU)).map (fun u => u n)) (Set.Iio (Real.exp (-1))) := by
      rw [Measure.map_apply (measurable_pi_apply n) measurableSet_Iio]; rfl
    rw [this, h, μU, Measure.restrict_apply measurableSet_Iio]
    have he : Set.Iio (Real.exp (-1)) ∩ Set.Ioo 0 1 = Set.Ioo 0 (Real.exp (-1)) := by
      ext y; simp only [Set.mem_inter_iff, Set.mem_Iio, Set.mem_Ioo]
      have : Real.exp (-1) < 1 := by
        have := Real.exp_lt_exp.mpr (show (-1:ℝ) < 0 by norm_num); simpa using this
      constructor
      · rintro ⟨h1, h2, _⟩; exact ⟨h2, h1⟩
      · rintro ⟨h1, h2⟩; exact ⟨h2, h1, by linarith⟩
    rw [he, Real.volume_Ioo, sub_zero]
  have hsum : (∑' n, (Measure.infinitePi (fun _ : ℕ => μU)) (s n)) = ∞ := by
    simp only [hmeas]
    rw [ENNReal.tsum_const_eq_top_of_ne_zero]
    simp [Real.exp_pos]
  have h1 := measure_limsup_eq_one hsm hind hsum
  have : ∀ᵐ u ∂(Measure.infinitePi (fun _ : ℕ => μU)), u ∈ limsup s atTop := by
    rw [ae_iff]
    have : {a | a ∉ limsup s atTop} = (limsup s atTop)ᶜ := rfl
    rw [this, prob_compl_eq_zero_iff (MeasurableSet.measurableSet_limsup hsm)]
    exact h1
  filter_upwards [this] with u hu
  rw [Filter.mem_limsup_iff_frequently_mem] at hu
  exact hu

lemma G_ae : ∀ᵐ u ∂(Measure.infinitePi (fun _ : ℕ => μU)), u ∈ G := by
  filter_upwards [ioo_ae, bc_ae] with u h1 h2
  refine ⟨h1, ?_⟩
  have hpos : ∀ k, 0 < -Real.log (u k) := fun k => by
    have := h1 k
    have := Real.log_neg this.1 this.2
    linarith
  intro M
  induction M with
  | zero => exact ⟨0, by simp⟩
  | succ M ih =>
    obtain ⟨n, hn⟩ := ih
    obtain ⟨k, hk, hk2⟩ := (Filter.frequently_atTop.mp h2) n
    refine ⟨k + 1, ?_⟩
    have hlog : 1 < -Real.log (u k) := by
      have hk2' : u k < Real.exp (-1) := hk2
      have h0 := (h1 k).1
      have : Real.log (u k) < -1 := by
        rw [Real.log_lt_iff_lt_exp h0]; exact hk2'
      linarith
    have hmono : ∑ i ∈ Finset.range n, -Real.log (u i) ≤ ∑ i ∈ Finset.range k, -Real.log (u i) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hk)
        (fun i _ _ => (hpos i).le)
    rw [Finset.sum_range_succ]
    push_cast
    linarith


noncomputable def cl (n : ℕ) (ω : Ωc) : ℝ := if ω.1 ∈ G then -Real.log (ω.1 n) else 1

lemma cl_pos (n : ℕ) (ω : Ωc) : 0 < cl n ω := by
  unfold cl; split_ifs with h
  · have h1 := h.1 n; have := Real.log_neg h1.1 h1.2; linarith
  · norm_num

def Yc (n : ℕ) (ω : Ωc) : Bool := xor n.bodd ω.2

lemma Yc_succ (n : ℕ) (ω : Ωc) : Yc (n+1) ω = !(Yc n ω) := by
  unfold Yc; rw [Nat.bodd_succ]; cases n.bodd <;> cases ω.2 <;> rfl

lemma Yc_zero (ω : Ωc) : Yc 0 ω = ω.2 := by
  unfold Yc; simp

noncomputable def jc (b : Bool) : PMF Bool := PMF.pure (!b)
def rc : Bool → ℝ := fun _ => 1

lemma jt_eq (n : ℕ) (ω : Ωc) : jumpTime rc Yc cl n ω = ∑ k ∈ Finset.range n, cl k ω := by
  induction n with
  | zero => rfl
  | succ n ih => simp [jumpTime, ih, Finset.sum_range_succ, rc]

lemma jt_strictMono (ω : Ωc) : StrictMono (fun n => jumpTime rc Yc cl n ω) := by
  apply strictMono_nat_of_lt_succ; intro n
  simp only [jt_eq, Finset.sum_range_succ]; linarith [cl_pos n ω]

lemma jt_tendsto (ω : Ωc) : Tendsto (fun n => jumpTime rc Yc cl n ω) atTop atTop := by
  by_cases h : ω.1 ∈ G
  · apply tendsto_atTop_atTop_of_monotone (jt_strictMono ω).monotone
    intro b
    obtain ⟨M, hM⟩ := exists_nat_ge b
    obtain ⟨n, hn⟩ := h.2 M
    refine ⟨n, ?_⟩
    rw [jt_eq]; simp only [cl, if_pos h]; linarith
  · have : (fun n => jumpTime rc Yc cl n ω) = fun n : ℕ => (n : ℝ) := by
      funext n; rw [jt_eq]; simp [cl, if_neg h]
    rw [this]; exact tendsto_natCast_atTop_atTop

noncomputable def Xc (t : ℝ) (ω : Ωc) : Bool := Yc (sSup {n | jumpTime rc Yc cl n ω ≤ t}) ω

lemma Xc_spec (ω : Ωc) (n : ℕ) (t : ℝ) (h1 : jumpTime rc Yc cl n ω ≤ t)
    (h2 : t < jumpTime rc Yc cl (n+1) ω) : Xc t ω = Yc n ω := by
  have : {k | jumpTime rc Yc cl k ω ≤ t} = Set.Iic n := by
    ext k; simp only [Set.mem_setOf_eq, Set.mem_Iic]
    constructor
    · intro hk; by_contra hc; push_neg at hc
      have := (jt_strictMono ω).monotone (Nat.succ_le_of_lt hc); linarith
    · intro hk; exact le_trans ((jt_strictMono ω).monotone hk) h1
  unfold Xc; rw [this, csSup_Iic]

lemma Xc_zero (ω : Ωc) : Xc 0 ω = ω.2 := by
  rw [Xc_spec ω 0 0 (by rw [jt_eq]; simp) (by rw [jt_eq]; simpa using cl_pos 0 ω), Yc_zero]

lemma jumpChain : IsJumpChain (Ω := Ωc) jc Yc := by
  intro n path y
  have hl : ∀ ω : Ωc, (∀ k : Fin (n+1), Yc k ω = path k) → Yc (n+1) ω = !(path (Fin.last n)) := by
    intro ω h; rw [Yc_succ]; have := h (Fin.last n); simp only [Fin.val_last] at this; rw [this]
  by_cases hy : y = !(path (Fin.last n))
  · have hset : {ω : Ωc | (∀ k : Fin (n+1), Yc k ω = path k) ∧ Yc (n+1) ω = y} =
        {ω | ∀ k : Fin (n+1), Yc k ω = path k} := by
      ext ω; simp only [Set.mem_setOf_eq]
      constructor
      · exact fun h => h.1
      · intro h; exact ⟨h, by rw [hl ω h, hy]⟩
    rw [hset, hy]; simp [jc]
  · have hset : {ω : Ωc | (∀ k : Fin (n+1), Yc k ω = path k) ∧ Yc (n+1) ω = y} = ∅ := by
      ext ω; simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      rintro ⟨h, h2⟩; exact hy (by rw [← h2, hl ω h])
    rw [hset]; simp [jc, PMF.pure_apply, hy]

lemma irr : Irreducible jc := by
  intro x y
  by_cases h : x = y
  · subst h; exact ⟨0, by simp [stepIter]⟩
  · refine ⟨1, ?_⟩
    have : y = !x := by cases x <;> cases y <;> simp_all
    subst this; simp [stepIter, jc]

lemma G_ae' : ∀ᵐ ω ∂(ℙ : Measure Ωc), ω.1 ∈ G := by
  have := G_ae; rw [← map_fst] at this; exact ae_of_ae_map measurable_fst.aemeasurable this

lemma cl_ae (n : ℕ) : (fun ω : Ωc => cl n ω) =ᵐ[ℙ] fun ω => -Real.log (ω.1 n) := by
  filter_upwards [G_ae'] with ω h; simp [cl, h]

lemma law_coord (n : ℕ) : (ℙ : Measure Ωc).map (fun ω => ω.1 n) = μU := by
  have : (fun ω : Ωc => ω.1 n) = (fun a : ℕ → ℝ => a n) ∘ Prod.fst := rfl
  rw [this, ← Measure.map_map (measurable_pi_apply _) measurable_fst, map_fst,
    Measure.infinitePi_map_eval]

lemma cl_exp (n : ℕ) (s : ℝ) (hs : 0 ≤ s) :
    ℙ {ω : Ωc | s < cl n ω} = ENNReal.ofReal (Real.exp (-s)) := by
  have h1 : ℙ {ω : Ωc | s < cl n ω} = ℙ {ω : Ωc | s < -Real.log (ω.1 n)} := by
    apply measure_congr
    filter_upwards [cl_ae n] with ω h
    change (s < cl n ω) = (s < -Real.log (ω.1 n)); rw [h]
  have hA : MeasurableSet {u : ℝ | s < -Real.log u} :=
    measurableSet_lt measurable_const (measurable_id.log.neg)
  have h2 : ℙ {ω : Ωc | s < -Real.log (ω.1 n)} = μU {u : ℝ | s < -Real.log u} := by
    rw [← law_coord n, Measure.map_apply (f := fun ω : Ωc => ω.1 n) ((measurable_pi_apply n).comp measurable_fst) hA]; rfl
  rw [h1, h2, μU, Measure.restrict_apply hA]
  have hexp : Real.exp (-s) ≤ 1 := by
    rw [Real.exp_le_one_iff]; linarith
  have he : {u : ℝ | s < -Real.log u} ∩ Set.Ioo 0 1 = Set.Ioo 0 (Real.exp (-s)) := by
    ext y; simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_Ioo]
    constructor
    · rintro ⟨h1, h2, h3⟩
      refine ⟨h2, ?_⟩
      have : Real.log y < -s := by linarith
      exact (Real.log_lt_iff_lt_exp h2).mp this
    · rintro ⟨h1, h2⟩
      refine ⟨?_, h1, by linarith⟩
      have := (Real.log_lt_iff_lt_exp h1).mpr h2
      linarith
  rw [he, Real.volume_Ioo, sub_zero]

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

lemma cl_iid : iIndepFun cl (ℙ : Measure Ωc) := by
  rw [iIndepFun_congr (fun n => cl_ae n)]
  refine iIndep_comp (ℙ : Measure Ωc) Prod.fst measurable_fst
    (fun n a => -Real.log (a n)) (fun n => ((measurable_pi_apply n).log).neg) ?_
  rw [map_fst]
  exact iIndepFun_infinitePi (P := fun _ : ℕ => μU) (X := fun _ u => -Real.log u)
    (fun _ => measurable_id.log.neg)

noncomputable def Fcl (u : ℕ → ℝ) : ℕ → ℝ := fun n => if u ∈ G then -Real.log (u n) else 1

lemma Fcl_meas : Measurable Fcl := by
  rw [measurable_pi_iff]; intro n
  show Measurable fun u : ℕ → ℝ => if u ∈ G then -Real.log (u n) else 1
  exact Measurable.ite G_meas ((measurable_pi_apply n).log.neg) measurable_const

def Fy (b : Bool) : ℕ → Bool := fun n => xor n.bodd b

lemma cl_indep : Indep (MeasurableSpace.comap (fun ω : Ωc => fun n => cl n ω) inferInstance)
    (MeasurableSpace.comap (fun ω : Ωc => fun n => Yc n ω) ⊤) ℙ := by
  refine indep_of_indep_of_le_left (indep_of_indep_of_le_right indep_cross ?_) ?_
  · show MeasurableSpace.comap (Fy ∘ Prod.snd) ⊤ ≤ _
    rw [← MeasurableSpace.comap_comp]
    apply MeasurableSpace.comap_mono
    intro t _
    exact MeasurableSet.of_discrete
  · show MeasurableSpace.comap (Fcl ∘ Prod.fst) _ ≤ _
    rw [← MeasurableSpace.comap_comp]
    exact MeasurableSpace.comap_mono Fcl_meas.comap_le

def Nc : ℝ → Ωc → Fin 1 → ℕ := fun _ _ _ => 0
def Zc : ℝ → Ωc → Fin 1 → ℕ := fun _ _ _ => 0

noncomputable def Mc : MarkovRepresentation Bool 1 1 Nc Zc where
  jump := jc
  rate := rc
  Y := Yc
  clock := cl
  X := Xc
  f := fun _ => (0, 0)
  rate_pos := fun _ => by simp [rc]
  jump_irrefl := fun x => by cases x <;> simp [jc]
  jump_chain := jumpChain
  clock_pos := cl_pos
  clock_exp := cl_exp
  clock_iid := cl_iid
  clock_indep_jumpChain := cl_indep
  nonexplosive := jt_tendsto
  sample_path := fun ω n t h1 h2 => Xc_spec ω n t h1 h2
  irreducible := irr
  sample_path_eq := fun t ω => rfl
  finite_fiber := fun z => Set.toFinite _
  empty_state := ⟨true, rfl⟩

def sdc : SPNData 1 1 1 where
  A := fun _ _ => 1
  B := fun _ _ => 1
  b := fun _ => 1
  A_binary := fun _ _ => Or.inr rfl
  B_binary := fun _ _ => Or.inr rfl
  A_col_nonzero := fun _ => ⟨0, rfl⟩
  B_col_nonzero := fun _ => ⟨0, rfl⟩
  b_pos := fun _ => one_pos

def datc : FluidEquationData 1 1 1 :=
  ⟨fun _ _ => 1, fun _ _ => 0, fun _ => 0, fun _ _ => 1, fun _ => 1, fun _ => 0⟩

def Ec : Fin 1 → ℝ → Ωc → ℕ := fun _ _ _ => 0
def vc : Fin 1 → ℕ → Ωc → ℝ := fun _ _ _ => 0
def φc : Fin 1 → ℕ → Ωc → Fin 1 → ℕ := fun _ _ _ _ => 1
def Psic : Bool → Fin 1 → ℕ → Ωc → ℝ × (Fin 1 → ℕ) := fun _ _ _ _ => (0, 0)

noncomputable def Fcx (x : Bool) (t : ℝ) (_ω : Ωc) (_j : Fin 1) : ℕ :=
  (if x then 2 else 1) * ⌊t⌋₊

lemma Fcx_mono (x : Bool) (ω : Ωc) (j : Fin 1) : Monotone fun t => Fcx x t ω j :=
  fun a b h => Nat.mul_le_mul_left _ (Nat.floor_mono h)

lemma rel (x : Bool) : SPNRelations sdc Ec vc φc (Mc.f x).1 (Psic x) (Mc.f x).2
    (Fcx x) (Fcx x) (fun _ _ _ => 0) (fun _ _ _ => 0) (fun t ω _ => Fcx x t ω 0)
    (fun _ _ _ => 0) where
  N_init := fun ω => rfl
  Z_init := fun ω => rfl
  S_init := fun ω => by funext j; simp [Fcx]
  S_mono := Fcx_mono x
  S_rightCont := by
    intro ω j t ht
    refine ⟨(⌊t⌋₊ : ℝ) + 1 - t, by linarith [Nat.lt_floor_add_one t], ?_⟩
    intro s hs
    simp only [Fcx]
    congr 1
    rw [Nat.floor_eq_iff (by linarith [hs.1])]
    exact ⟨le_trans (Nat.floor_le ht) hs.1, by linarith [hs.2]⟩
  F_init := fun ω => by funext j; simp [Fcx]
  F_mono := Fcx_mono x
  service_counts := fun t ω j _ => by simp [Mc]
  departures := fun t ω i _ => by simp [sdc]
  buffer_contents := fun t ω i _ => by
    simp [Mc, cumulativeOutput, delayedTerm, φc, Ec]
  availability := fun t ω i _ => by simp
  T_init := fun ω => rfl
  T_mono := fun ω j => monotone_const
  T_capacity := fun ω s t k _ hst => by simp [sdc]; linarith
  service_bound := ⟨0, fun _ _ _ => le_rfl⟩
  effort_completions := fun t ω j _ => by
    simp [delayedWalk, delayedTerm, vc, Mc]

lemma pool_indep_c :
    Indep (MeasurableSpace.comap
      (fun ω : Ωc => fun p : {p // p ∈ (∅ : Finset (Ωc → ℝ × (Fin 1 → ℕ)))} => p.1 ω)
      inferInstance)
      (MeasurableSpace.comap
        (fun ω => (fun i t => Ec i t ω, fun j ℓ => (vc j ℓ ω, φc j ℓ ω))) inferInstance) ℙ := by
  have hc : (fun ω : Ωc => fun p : {p // p ∈ (∅ : Finset (Ωc → ℝ × (Fin 1 → ℕ)))} => p.1 ω) =
      fun _ => fun p => absurd p.2 (Finset.notMem_empty _) := by
    funext ω p; exact absurd p.2 (Finset.notMem_empty _)
  rw [hc, MeasurableSpace.comap_const]
  exact indep_bot_left _

lemma init_supp (x : Bool) : (ℙ : Measure Ωc) {ω | Mc.X 0 ω = x} ≠ 0 := by
  have : {ω : Ωc | Mc.X 0 ω = x} = Set.univ ×ˢ {x} := by
    ext ω; simp [Mc, Xc_zero]
  rw [this, vol_eq, Measure.prod_prod, measure_univ, one_mul]
  simp [μB, PMF.toMeasure_apply_singleton]

noncomputable def famc : SPNProcessFamily Mc sdc datc Ec vc φc where
  data_B := rfl
  data_A := rfl
  data_b := rfl
  Psi := Psic
  S := Fcx
  F := Fcx
  Nx := fun _ _ _ _ => 0
  T := fun _ _ _ _ => 0
  D := fun x t ω _ => Fcx x t ω 0
  Zx := fun _ _ _ _ => 0
  relations := rel
  service_bound := ⟨0, fun _ _ _ _ => le_rfl⟩
  pool := ∅
  Psi_mem_pool := fun x j k hk => by simp [Mc] at hk
  pool_indep := pool_indep_c
  initial_support := init_supp
  law := by
    intro x t z _
    haveI := cond_isProbabilityMeasure (init_supp x)
    by_cases hz : (fun _ => 0 : Fin 1 → ℕ) = z
    · have h1 : {ω : Ωc | (fun _ => 0 : Fin 1 → ℕ) = z} = Set.univ := by simp [hz]
      change ℙ {ω : Ωc | (fun _ => 0 : Fin 1 → ℕ) = z} =
        (ℙ[|{ω : Ωc | Mc.X 0 ω = x}]) {ω : Ωc | (fun _ => 0 : Fin 1 → ℕ) = z}
      rw [h1, measure_univ, measure_univ]
    · have h1 : {ω : Ωc | (fun _ => 0 : Fin 1 → ℕ) = z} = ∅ := by simp [hz]
      change ℙ {ω : Ωc | (fun _ => 0 : Fin 1 → ℕ) = z} =
        (ℙ[|{ω : Ωc | Mc.X 0 ω = x}]) {ω : Ωc | (fun _ => 0 : Fin 1 → ℕ) = z}
      rw [h1, measure_empty, measure_empty]

lemma Fval (b : Bool) (n : ℕ) (hn : 1 ≤ n) (ω : Ωc) :
    ((n : ℝ))⁻¹ * (Fcx b ((n : ℝ) * 1) ω 0 : ℝ) = if b then 2 else 1 := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  simp only [Fcx, mul_one, Nat.floor_natCast]
  cases b <;> simp <;> field_simp

end FTCex

open FTCex in
theorem ft_disproof_core : ¬ (∀ {Xstate : Type} [Countable Xstate] {Ω : Type} [MeasureSpace Ω] {I J K : ℕ}
    {N : ℝ → Ω → Fin J → ℕ} {Z : ℝ → Ω → Fin I → ℕ}
    {Mrep : MarkovRepresentation Xstate I J N Z} {sd : SPNData I J K}
    {dat : FluidEquationData I J K} {E : Fin I → ℝ → Ω → ℕ} {v : Fin J → ℕ → Ω → ℝ}
    {φ : Fin J → ℕ → Ω → Fin I → ℕ} (fam : SPNProcessFamily Mrep sd dat E v φ) (ω : Ω)
    (h215 :
      ∀ j, Tendsto (fun n : ℕ => (∑ ℓ ∈ Finset.range n, v j ℓ ω) / n) atTop (nhds (dat.m j)))
    (h638 :
      ∀ j, Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ⨆ ℓ ∈ Finset.range n, v j ℓ ω) atTop
        (nhds 0))
    (x : ℕ → Xstate) (r : ℕ → ℝ) (hr : Tendsto r atTop atTop) (t : ℝ) (ht : 0 ≤ t) (j : Fin J),
    ((∃ Fhj : ℝ, Tendsto (fun n => (r n)⁻¹ * (fam.F (x n) (r n * t) ω j : ℝ)) atTop (nhds Fhj)) ↔
     (∃ Thj : ℝ, Tendsto (fun n => (r n)⁻¹ * fam.T (x n) (r n * t) ω j) atTop (nhds Thj))) ∧
    (∀ Fhj Thj : ℝ,
      Tendsto (fun n => (r n)⁻¹ * (fam.F (x n) (r n * t) ω j : ℝ)) atTop (nhds Fhj) →
      Tendsto (fun n => (r n)⁻¹ * fam.T (x n) (r n * t) ω j) atTop (nhds Thj) →
      dat.m j * Fhj = Thj)) := by
  intro h
  let ω0 : Ωc := (fun _ => 1/2, true)
  have h215 : ∀ j, Tendsto (fun n : ℕ => (∑ ℓ ∈ Finset.range n, vc j ℓ ω0) / n) atTop
      (nhds (datc.m j)) := fun j => by simpa [vc, datc] using tendsto_const_nhds
  have h638 : ∀ j, Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ⨆ ℓ ∈ Finset.range n, vc j ℓ ω0) atTop
      (nhds 0) := fun j => by simpa [vc] using tendsto_const_nhds
  have hh := (@h Bool _ Ωc _ 1 1 1 Nc Zc Mc sdc datc Ec vc φc famc ω0 h215 h638
    (fun n => n.bodd) (fun n => (n : ℝ)) tendsto_natCast_atTop_atTop 1 zero_le_one 0).1
  obtain ⟨Fh, hF⟩ := hh.mpr ⟨0, by simpa [famc] using tendsto_const_nhds⟩
  have hF' : Tendsto (fun n : ℕ => ((n : ℝ))⁻¹ * (Fcx n.bodd ((n : ℝ) * 1) ω0 0 : ℝ)) atTop
      (nhds Fh) := hF
  have he : Tendsto (fun k : ℕ => 2 * k + 2) atTop atTop :=
    tendsto_atTop_atTop.mpr fun b => ⟨b, fun a ha => by omega⟩
  have ho : Tendsto (fun k : ℕ => 2 * k + 1) atTop atTop :=
    tendsto_atTop_atTop.mpr fun b => ⟨b, fun a ha => by omega⟩
  have h1 := hF'.comp he
  have h2 := hF'.comp ho
  have e1 : (fun n : ℕ => ((n : ℝ))⁻¹ * (Fcx n.bodd ((n : ℝ) * 1) ω0 0 : ℝ)) ∘
      (fun k : ℕ => 2 * k + 2) = fun _ => (1 : ℝ) := by
    funext k
    simp only [Function.comp]
    rw [Fval _ _ (by omega)]
    have : (2 * k + 2).bodd = false := by
      rw [show 2 * k + 2 = 2 * (k + 1) by ring, Nat.bodd_mul]; simp
    rw [this]; rfl
  have e2 : (fun n : ℕ => ((n : ℝ))⁻¹ * (Fcx n.bodd ((n : ℝ) * 1) ω0 0 : ℝ)) ∘
      (fun k : ℕ => 2 * k + 1) = fun _ => (2 : ℝ) := by
    funext k
    simp only [Function.comp]
    rw [Fval _ _ (by omega)]
    have : (2 * k + 1).bodd = true := by
      rw [Nat.bodd_succ, Nat.bodd_mul]; simp
    rw [this]; rfl
  rw [e1] at h1
  rw [e2] at h2
  have := tendsto_nhds_unique (tendsto_const_nhds) h1
  have := tendsto_nhds_unique (tendsto_const_nhds) h2
  linarith


end ProcessingNetworks.FluidStability

open MeasureTheory ProbabilityTheory Filter ProcessingNetworks.Stability ProcessingNetworks.FluidStability

theorem solution : ¬ (∀ {Xstate : Type} [Countable Xstate] {Ω : Type} [MeasureSpace Ω] {I J K : ℕ}
    {N : ℝ → Ω → Fin J → ℕ} {Z : ℝ → Ω → Fin I → ℕ}
    {Mrep : MarkovRepresentation Xstate I J N Z} {sd : SPNData I J K}
    {dat : FluidEquationData I J K} {E : Fin I → ℝ → Ω → ℕ} {v : Fin J → ℕ → Ω → ℝ}
    {φ : Fin J → ℕ → Ω → Fin I → ℕ} (fam : SPNProcessFamily Mrep sd dat E v φ) (ω : Ω)
    (h215 :
      ∀ j, Tendsto (fun n : ℕ => (∑ ℓ ∈ Finset.range n, v j ℓ ω) / n) atTop (nhds (dat.m j)))
    (h638 :
      ∀ j, Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ⨆ ℓ ∈ Finset.range n, v j ℓ ω) atTop
        (nhds 0))
    (x : ℕ → Xstate) (r : ℕ → ℝ) (hr : Tendsto r atTop atTop) (t : ℝ) (ht : 0 ≤ t) (j : Fin J),
    ((∃ Fhj : ℝ, Tendsto (fun n => (r n)⁻¹ * (fam.F (x n) (r n * t) ω j : ℝ)) atTop (nhds Fhj)) ↔
     (∃ Thj : ℝ, Tendsto (fun n => (r n)⁻¹ * fam.T (x n) (r n * t) ω j) atTop (nhds Thj))) ∧
    (∀ Fhj Thj : ℝ,
      Tendsto (fun n => (r n)⁻¹ * (fam.F (x n) (r n * t) ω j : ℝ)) atTop (nhds Fhj) →
      Tendsto (fun n => (r n)⁻¹ * fam.T (x n) (r n * t) ω j) atTop (nhds Thj) →
      dat.m j * Fhj = Thj)) :=
  ProcessingNetworks.FluidStability.ft_disproof_core
