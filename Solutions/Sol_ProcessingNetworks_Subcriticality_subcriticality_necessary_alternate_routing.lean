import Mathlib
import Definitions.Def_ProcessingNetworks_Stability_BaselineAssumptions
import Definitions.Def_ProcessingNetworks_Stability_MarkovRepresentation
import Definitions.Def_ProcessingNetworks_Stability_StabilityConditions
import Definitions.Def_ProcessingNetworks_Stability_Stable
import Definitions.Def_ProcessingNetworks_Stability_SPNModel
import Definitions.Def_ProcessingNetworks_Subcriticality_SPNPlanningData
import Definitions.Def_ProcessingNetworks_Subcriticality_StaticPlanningProblem
import Definitions.Def_ProcessingNetworks_Subcriticality_BaselineAssumptionsMArP

open MeasureTheory ProbabilityTheory ProcessingNetworks.Stability
open scoped NNReal

namespace ProcessingNetworks.Subcriticality

universe u v

open MeasureTheory ProbabilityTheory Filter ProcessingNetworks.Stability

instance cex_expProb : IsProbabilityMeasure (expMeasure 1) := isProbabilityMeasure_expMeasure one_pos

noncomputable def cexBase : Measure (ULift.{u} ℝ) := (expMeasure 1).map ULift.up

instance cexBase_prob : IsProbabilityMeasure cexBase.{u} :=
  Measure.isProbabilityMeasure_map measurable_up.aemeasurable

abbrev CΩ : Type u := ℕ → ULift.{u} ℝ

noncomputable instance cexMS : MeasureSpace CΩ.{u} := ⟨Measure.infinitePi fun _ => cexBase.{u}⟩

instance cexProb : IsProbabilityMeasure (ℙ : Measure CΩ.{u}) := by
  show IsProbabilityMeasure (Measure.infinitePi fun _ => cexBase.{u}); infer_instance

lemma cex_coord (n : ℕ) {s : Set ℝ} (hs : MeasurableSet s) :
    (ℙ : Measure CΩ.{u}) {x | (x n).down ∈ s} = expMeasure 1 s := by
  have hm : Measurable (fun x : CΩ.{u} => x n) := measurable_pi_apply n
  have : {x : CΩ.{u} | (x n).down ∈ s} = (fun x : CΩ.{u} => x n) ⁻¹' (ULift.down ⁻¹' s) := rfl
  rw [this, ← Measure.map_apply hm (measurable_down hs)]
  show (Measure.map (fun x : CΩ.{u} => x n) (Measure.infinitePi fun _ => cexBase.{u})) _ = _
  rw [Measure.infinitePi_map_eval, cexBase, Measure.map_apply measurable_up (measurable_down hs)]
  rfl

lemma exp_Iic (s : ℝ) (hs : 0 ≤ s) : expMeasure 1 (Set.Iic s) = ENNReal.ofReal (1 - Real.exp (-s)) := by
  rw [← ofReal_cdf, cdf_expMeasure_eq one_pos, if_pos hs, one_mul]

lemma exp_Ioi (s : ℝ) (hs : 0 ≤ s) : expMeasure 1 (Set.Ioi s) = ENNReal.ofReal (Real.exp (-s)) := by
  rw [← Set.compl_Iic, prob_compl_eq_one_sub measurableSet_Iic, exp_Iic s hs]
  have h1 : Real.exp (-s) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _ (by linarith)]
  congr 1; ring

lemma exp_Iic0 : expMeasure 1 (Set.Iic 0) = 0 := by
  rw [exp_Iic 0 le_rfl]; simp

lemma cex_indep : iIndepFun (fun n (x : CΩ.{u}) => (x n).down) ℙ :=
  iIndepFun_infinitePi (P := fun _ => cexBase.{u}) (X := fun _ => ULift.down) (fun _ => measurable_down)

lemma cex_ae_pos : ∀ᵐ x ∂(ℙ : Measure CΩ.{u}), ∀ n, 0 < (x n).down := by
  rw [ae_all_iff]; intro n
  rw [ae_iff]
  have : {x : CΩ.{u} | ¬ 0 < (x n).down} = {x | (x n).down ∈ Set.Iic 0} := by
    ext x; simp
  rw [this, cex_coord n measurableSet_Iic, exp_Iic0]

lemma cex_ae_freq : ∀ᵐ x ∂(ℙ : Measure CΩ.{u}), ∃ᶠ n in atTop, 1 < (x n).down := by
  set s : ℕ → Set CΩ.{u} := fun n => {x | (x n).down ∈ Set.Ioi 1} with hs
  have hsm : ∀ n, MeasurableSet (s n) := fun n =>
    (measurable_down.comp (measurable_pi_apply n)) measurableSet_Ioi
  have hind : iIndepSet s ℙ := by
    rw [iIndepSet_iff_iIndep]
    refine iIndep_of_iIndep_of_le ((iIndepFun_iff_iIndep _ _ _).1 cex_indep) (fun n => ?_)
    refine MeasurableSpace.generateFrom_le ?_
    rintro t rfl
    exact ⟨Set.Ioi 1, measurableSet_Ioi, rfl⟩
  have hsum : (∑' n, (ℙ : Measure CΩ.{u}) (s n)) = ⊤ := by
    simp only [hs, cex_coord _ measurableSet_Ioi, exp_Ioi 1 zero_le_one]
    exact ENNReal.tsum_const_eq_top_of_ne_zero (by simp [Real.exp_pos])
  have h1 := measure_limsup_eq_one hsm hind hsum
  have h2 : ∀ᵐ x ∂(ℙ : Measure CΩ.{u}), x ∈ limsup s atTop := by
    have hm : MeasurableSet (limsup s atTop) := by
      rw [limsup_eq_iInf_iSup_of_nat]
      exact MeasurableSet.iInter fun n => MeasurableSet.iUnion fun i => MeasurableSet.iUnion fun _ => hsm i
    rw [ae_iff]
    exact (prob_compl_eq_zero_iff hm).2 h1
  filter_upwards [h2] with x hx
  rw [limsup_eq_iInf_iSup_of_nat] at hx
  simp only [Set.iInf_eq_iInter, Set.iSup_eq_iUnion, Set.mem_iInter, Set.mem_iUnion] at hx
  rw [Filter.frequently_atTop]
  intro a
  obtain ⟨b, hb, hx⟩ := hx a
  exact ⟨b, hb, hx⟩

def cexGood (x : CΩ.{u}) : Prop :=
  (∀ n, 0 < (x n).down) ∧ Tendsto (fun n => ∑ k ∈ Finset.range n, (x k).down) atTop atTop

lemma tendsto_of_freq {a : ℕ → ℝ} (hpos : ∀ n, 0 < a n) (hf : ∃ᶠ n in atTop, 1 < a n) :
    Tendsto (fun n => ∑ k ∈ Finset.range n, a k) atTop atTop := by
  have hmono : Monotone (fun n => ∑ k ∈ Finset.range n, a k) := by
    intro m n hmn
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hmn) (fun i _ _ => (hpos i).le)
  have key : ∀ m : ℕ, ∃ N, (m : ℝ) ≤ ∑ k ∈ Finset.range N, a k := by
    intro m
    induction m with
    | zero => exact ⟨0, by simp⟩
    | succ m ih =>
      obtain ⟨N, hN⟩ := ih
      obtain ⟨n, hn, h1⟩ := Filter.frequently_atTop.1 hf N
      refine ⟨n + 1, ?_⟩
      rw [Finset.sum_range_succ]
      have := hmono hn
      push_cast
      linarith
  refine tendsto_atTop_atTop_of_monotone hmono (fun b => ?_)
  obtain ⟨m, hm⟩ := exists_nat_ge b
  obtain ⟨N, hN⟩ := key m
  exact ⟨N, hm.trans hN⟩

lemma cex_ae_good : ∀ᵐ x ∂(ℙ : Measure CΩ.{u}), cexGood x := by
  filter_upwards [cex_ae_pos, cex_ae_freq] with x h1 h2
  exact ⟨h1, tendsto_of_freq h1 h2⟩

open Classical in
noncomputable def cexClock (n : ℕ) (x : CΩ.{u}) : ℝ := if cexGood x then (x n).down else 1

lemma cexClock_ae (n : ℕ) : cexClock n =ᵐ[(ℙ : Measure CΩ.{u})] fun x => (x n).down := by
  filter_upwards [cex_ae_good] with x hx
  simp [cexClock, hx]

lemma cexClock_pos (n : ℕ) (x : CΩ.{u}) : 0 < cexClock n x := by
  unfold cexClock; split_ifs with h
  · exact h.1 n
  · exact one_pos

lemma cexClock_sum (x : CΩ.{u}) :
    Tendsto (fun n => ∑ k ∈ Finset.range n, cexClock k x) atTop atTop := by
  by_cases h : cexGood x
  · simpa [cexClock, h] using h.2
  · simp only [cexClock, h, if_false, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
    exact tendsto_natCast_atTop_atTop

lemma cexClock_iid : iIndepFun cexClock (ℙ : Measure CΩ.{u}) :=
  (iIndepFun_congr (fun n => (cexClock_ae n).symm)).1 cex_indep

lemma cexClock_exp (n : ℕ) (s : ℝ) (hs : 0 ≤ s) :
    (ℙ : Measure CΩ.{u}) {x | s < cexClock n x} = ENNReal.ofReal (Real.exp (-s)) := by
  have : {x : CΩ.{u} | s < cexClock n x} =ᵐ[ℙ] {x | (x n).down ∈ Set.Ioi s} := by
    filter_upwards [cexClock_ae n] with x hx
    change (s < cexClock n x) = ((x n).down ∈ Set.Ioi s)
    rw [hx]; rfl
  rw [measure_congr this, cex_coord n measurableSet_Ioi, exp_Ioi s hs]

abbrev CX : Type v := ULift.{v} Bool

def cfl (x : CX.{v}) : CX.{v} := ULift.up (!x.down)

lemma ne_iff_cfl (x y : CX.{v}) : y ≠ x ↔ y = cfl x := by
  rcases x with ⟨a⟩; rcases y with ⟨b⟩
  cases a <;> cases b <;> simp [cfl]

lemma cfl_cfl (x : CX.{v}) : cfl (cfl x) = x := by
  rcases x with ⟨a⟩; simp [cfl]

lemma cfl_ne (x : CX.{v}) : cfl x ≠ x := (ne_iff_cfl x (cfl x)).2 rfl

noncomputable def cJump (x : CX.{v}) : PMF CX.{v} := PMF.pure (cfl x)

lemma cJump_apply (x y : CX.{v}) : cJump x y = if y = cfl x then 1 else 0 := by
  simp [cJump, PMF.pure_apply]

def cY (n : ℕ) (_ : CΩ.{u}) : CX.{v} := ULift.up n.bodd

lemma cY_succ (n : ℕ) (ω : CΩ.{u}) : cY.{u, v} (n + 1) ω = cfl (cY n ω) := by
  simp [cY, cfl, Nat.bodd_succ]

lemma jumpTime_one (Y : ℕ → CΩ.{u} → CX.{v}) (c : ℕ → CΩ.{u} → ℝ) (n : ℕ) (ω : CΩ.{u}) :
    jumpTime (fun _ => (1 : ℝ)) Y c n ω = ∑ k ∈ Finset.range n, c k ω := by
  induction n with
  | zero => simp [jumpTime]
  | succ n ih => simp [jumpTime, Finset.sum_range_succ, ih]

open Classical in
noncomputable def cXt (t : ℝ) (ω : CΩ.{u}) : CX.{v} :=
  if h : ∃ m, t < ∑ k ∈ Finset.range (m + 1), cexClock k ω then cY.{u, v} (Nat.find h) ω
  else cY 0 ω

lemma cex_mono (ω : CΩ.{u}) : Monotone (fun n => ∑ k ∈ Finset.range n, cexClock k ω) := by
  intro m n hmn
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hmn)
    (fun i _ _ => (cexClock_pos i ω).le)

lemma cXt_eq (ω : CΩ.{u}) (n : ℕ) (t : ℝ) (h1 : ∑ k ∈ Finset.range n, cexClock k ω ≤ t)
    (h2 : t < ∑ k ∈ Finset.range (n + 1), cexClock k ω) : cXt.{u, v} t ω = cY n ω := by
  have h : ∃ m, t < ∑ k ∈ Finset.range (m + 1), cexClock k ω := ⟨n, h2⟩
  rw [cXt, dif_pos h]
  congr 1
  rw [Nat.find_eq_iff]
  refine ⟨h2, fun m hm => not_lt.2 (le_trans (cex_mono ω (by omega)) h1)⟩

lemma cJump_chain : IsJumpChain (cJump.{v}) (cY.{u, v}) := by
  intro n path y
  by_cases hp : ∀ k : Fin (n + 1), cY.{u, v} k (fun _ => ULift.up 0) = path k
  · have hlast : path (Fin.last n) = cY.{u, v} n (fun _ => ULift.up 0) := by
      rw [← hp (Fin.last n)]; simp
    have e2 : {ω : CΩ.{u} | ∀ k : Fin (n + 1), cY.{u, v} k ω = path k} = Set.univ := by
      ext ω; simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]; exact hp
    by_cases hy : cY.{u, v} (n + 1) (fun _ => ULift.up 0) = y
    · have e1 : {ω : CΩ.{u} | (∀ k : Fin (n + 1), cY.{u, v} k ω = path k) ∧
          cY.{u, v} (n + 1) ω = y} = Set.univ := by
        ext ω; simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]; exact ⟨hp, hy⟩
      rw [e1, e2, hlast, cJump_apply, if_pos (by rw [← hy, cY_succ])]; simp
    · have e1 : {ω : CΩ.{u} | (∀ k : Fin (n + 1), cY.{u, v} k ω = path k) ∧
          cY.{u, v} (n + 1) ω = y} = ∅ := by
        ext ω; simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
        intro _; exact hy
      rw [e1, e2, hlast, cJump_apply, if_neg (by rw [← cY_succ]; exact fun h => hy h.symm)]; simp
  · have e1 : {ω : CΩ.{u} | (∀ k : Fin (n + 1), cY.{u, v} k ω = path k) ∧
        cY.{u, v} (n + 1) ω = y} = ∅ := by
      ext ω; simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
      intro h; exact absurd h hp
    have e2 : {ω : CΩ.{u} | ∀ k : Fin (n + 1), cY.{u, v} k ω = path k} = ∅ := by
      ext ω; simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      intro h; exact hp h
    rw [e1, e2]; simp

lemma taboo1 (x y : CX.{v}) : tabooProb cJump x 1 y = if y = x then 0 else 1 := by
  simp only [tabooProb]
  split_ifs with h
  · rfl
  · rw [tsum_eq_single x (fun z hz => by simp [hz])]
    simp [cJump_apply, (ne_iff_cfl x y).1 h]

lemma taboo2 (x : CX.{v}) (n : ℕ) (y : CX.{v}) : tabooProb cJump x (n + 2) y = 0 := by
  induction n generalizing y with
  | zero =>
    show tabooProb cJump x (1 + 1) y = 0
    rw [tabooProb]
    split_ifs with h
    · rfl
    · have : ∀ z, tabooProb cJump x 1 z * cJump z y = 0 := by
        intro z
        rw [taboo1, cJump_apply]
        by_cases hz : z = x
        · simp [hz]
        · have hz' := (ne_iff_cfl x z).1 hz
          have : y ≠ cfl z := by rw [hz', cfl_cfl]; exact h
          simp [hz, this]
      simp [this]
  | succ n ih =>
    show tabooProb cJump x ((n + 2) + 1) y = 0
    rw [tabooProb]
    simp [ih]

lemma cex_posrec : PositiveRecurrent (cJump.{v}) (fun _ => (1 : ℝ)) := by
  intro x
  have f0 : firstReturnProb cJump x 0 = 0 := by
    simp only [firstReturnProb, tabooProb]
    rw [tsum_eq_single x (fun z hz => by simp [hz])]
    simp [cJump_apply, (cfl_ne x).symm]
  have f1 : firstReturnProb cJump x 1 = 1 := by
    simp only [firstReturnProb]
    rw [tsum_eq_single (cfl x) (fun z hz => by
      have : z = x := by
        by_contra h; exact hz ((ne_iff_cfl x z).1 h)
      simp [taboo1, this])]
    simp [taboo1, cfl_ne, cJump_apply, cfl_cfl]
  have f2 : ∀ n, firstReturnProb cJump x (n + 2) = 0 := by
    intro n; simp [firstReturnProb, taboo2]
  refine ⟨?_, ?_⟩
  · unfold Recurrent
    rw [tsum_eq_single 1 (fun n hn => by
      rcases n with _ | _ | n
      · exact f0
      · exact absurd rfl hn
      · exact f2 n)]
    exact f1
  · unfold meanReturnTime
    have g0 : ∑' y, tabooProb cJump x 0 y * ENNReal.ofReal ((fun _ => (1 : ℝ)) y)⁻¹ = 1 := by
      simp only [inv_one, ENNReal.ofReal_one, mul_one]
      rw [tsum_eq_single x (fun z hz => by simp [tabooProb, hz])]
      simp [tabooProb]
    have g1 : ∑' y, tabooProb cJump x 1 y * ENNReal.ofReal ((fun _ => (1 : ℝ)) y)⁻¹ = 1 := by
      simp only [inv_one, ENNReal.ofReal_one, mul_one]
      rw [tsum_eq_single (cfl x) (fun z hz => by
        have : z = x := by
          by_contra h; exact hz ((ne_iff_cfl x z).1 h)
        simp [taboo1, this])]
      simp [taboo1, cfl_ne]
    rw [tsum_eq_sum (s := Finset.range 2) (fun n hn => by
      rcases n with _ | _ | n
      · simp at hn
      · simp at hn
      · simp [taboo2])]
    rw [Finset.sum_range_succ, Finset.sum_range_one, g0, g1]; simp

def cN : ℝ → CΩ.{u} → Fin 0 → ℕ := fun _ _ _ => 0

noncomputable def cM : MarkovRepresentation CX.{v} 0 0 cN.{u} cN.{u} where
  jump := cJump
  rate := fun _ => 1
  Y := cY
  clock := cexClock
  X := cXt
  f := fun _ => (0, 0)
  rate_pos := fun _ => one_pos
  jump_irrefl := fun x => by rw [cJump_apply, if_neg (cfl_ne x).symm]
  jump_chain := cJump_chain
  clock_pos := cexClock_pos
  clock_exp := cexClock_exp
  clock_iid := cexClock_iid
  clock_indep_jumpChain := by
    show Indep _ (MeasurableSpace.comap (fun _ : CΩ.{u} => fun n : ℕ => (ULift.up n.bodd : CX.{v})) ⊤) _
    rw [MeasurableSpace.comap_const]; exact indep_bot_right _
  nonexplosive := fun ω => by simpa [jumpTime_one] using cexClock_sum ω
  sample_path := fun ω n t h1 h2 => by
    rw [jumpTime_one] at h1 h2
    exact cXt_eq ω n t h1 h2
  irreducible := by
    intro x y
    by_cases h : y = x
    · subst h; exact ⟨0, by simp [stepIter]⟩
    · refine ⟨1, ?_⟩
      have : y = cfl x := (ne_iff_cfl x y).1 h
      subst this
      simp [stepIter, cJump]
  sample_path_eq := fun _ _ => Subsingleton.elim _ _
  finite_fiber := fun _ => Set.toFinite _
  empty_state := ⟨ULift.up false, Subsingleton.elim _ _⟩

lemma cM_stable : IsStable cM.{u, v} := cex_posrec

lemma iIndep_triv {Ω ι : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (m : ι → MeasurableSpace Ω) (hm : ∀ i, m i = ⊥) : iIndep m μ := by
  rw [iIndep_iff]
  intro s f hf
  by_cases h : ∃ i ∈ s, f i = ∅
  · obtain ⟨i, hi, hfi⟩ := h
    have h0 : (⋂ i ∈ s, f i) = ∅ := Set.subset_eq_empty (Set.biInter_subset_of_mem hi) hfi
    rw [h0, measure_empty]
    exact (Finset.prod_eq_zero hi (by rw [hfi, measure_empty])).symm
  · push_neg at h
    have hu : ∀ i ∈ s, f i = Set.univ := by
      intro i hi
      have := hf i hi
      rw [hm i, MeasurableSpace.measurableSet_bot_iff] at this
      exact this.resolve_left (Set.nonempty_iff_ne_empty.1 (h i hi))
    have h1 : (⋂ i ∈ s, f i) = Set.univ := by
      ext x; simp only [Set.mem_iInter, Set.mem_univ, iff_true]; intro i hi; rw [hu i hi]; trivial
    rw [h1, measure_univ]
    exact (Finset.prod_eq_one fun i hi => by rw [hu i hi, measure_univ]).symm

lemma comap_subsingleton {α β : Type*} [Subsingleton β] [Inhabited β] [mβ : MeasurableSpace β]
    (f : α → β) : MeasurableSpace.comap f mβ = ⊥ := by
  have : f = fun _ => default := funext fun _ => Subsingleton.elim _ _
  rw [this, MeasurableSpace.comap_const]

lemma tendsto_subsingleton {α β : Type*} [TopologicalSpace β] [Subsingleton β] (f : α → β)
    (l : Filter α) (b : β) : Tendsto f l (nhds b) := by
  intro s hs
  have : f ⁻¹' s = Set.univ := Set.eq_univ_of_forall fun a => by
    rw [Set.mem_preimage, Subsingleton.elim (f a) b]; exact mem_of_mem_nhds hs
  rw [Filter.mem_map, this]; exact univ_mem

lemma prob_tendsto_triv {α β : Type*} [TopologicalSpace β] [Subsingleton β] (f : CΩ.{u} → α → β)
    (l : Filter α) (b : β) : (ℙ : Measure CΩ.{u}) {ω | Tendsto (f ω) l (nhds b)} = 1 := by
  have : {ω | Tendsto (f ω) l (nhds b)} = Set.univ :=
    Set.eq_univ_of_forall (fun ω => tendsto_subsingleton (f ω) l b)
  rw [this, measure_univ]

lemma not_subcrit {D : SPNPlanningData 0 0 0} {lam : Fin 0 → ℝ} : lam ∉ SubcriticalRegion D := by
  rintro ⟨_, γ, hγ, _⟩
  have : γ - 1 ∈ {γ : ℝ | ∃ x, SPPFeasible D γ lam x} :=
    ⟨fun j => j.elim0, funext fun i => i.elim0, fun j => j.elim0, fun k => k.elim0⟩
  linarith [hγ.2 this]

lemma not_aug_subcrit {D : SPNPlanningData 0 0 0} {G : Matrix (Fin 0) (Fin 0) ℝ} {nu : Fin 0 → ℝ} :
    ¬ IsAugmentedSubcritical D G nu := by
  rintro ⟨γ, hγ, _⟩
  have : γ - 1 ∈ {γ : ℝ | ∃ phi x, AugmentedSPPFeasible D G γ nu phi x} :=
    ⟨fun l => l.elim0, fun j => j.elim0, fun l => l.elim0, fun l => l.elim0,
      funext fun i => i.elim0, fun l => l.elim0, fun j => j.elim0, fun k => k.elim0⟩
  linarith [hγ.2 this]

def cDat : SPNData 0 0 0 where
  A := 0
  B := 0
  b := fun k => k.elim0
  A_binary := fun k => k.elim0
  B_binary := fun i => i.elim0
  A_col_nonzero := fun j => j.elim0
  B_col_nonzero := fun j => j.elim0
  b_pos := fun k => k.elim0

lemma cPVA : ProcessingVariableAssumptions (Ω := CΩ.{u}) 0 0 (fun i => i.elim0) (fun j => j.elim0)
    (fun j => j.elim0) (fun j => j.elim0) (fun j => j.elim0) (fun j => j.elim0) where
  processing_iid := fun j => j.elim0
  processing_positive := fun j => j.elim0
  mean_service_time := fun j => j.elim0
  mean_output := fun j => j.elim0
  phase_type := fun j => j.elim0
  mutual_independence := iIndep_triv _ _ (fun i => by
    fin_cases i <;> exact comap_subsingleton _)

lemma cBasic : IsBasicSPN (Ω := CΩ.{u}) cDat (fun i => i.elim0) (fun j => j.elim0) (fun j => j.elim0)
    (fun j => j.elim0) (fun j => j.elim0) (fun i => i.elim0) cN cN cN (fun _ _ j => j.elim0)
    (fun _ _ i => i.elim0) cN where
  N_init := fun _ => funext fun j => j.elim0
  Z_init := fun _ => funext fun j => j.elim0
  S_init := fun _ => funext fun j => j.elim0
  S_mono := fun _ j => j.elim0
  S_rightCont := fun _ j => j.elim0
  F_init := fun _ => funext fun j => j.elim0
  F_mono := fun _ j => j.elim0
  service_counts := fun _ _ j => j.elim0
  departures := fun _ _ i => i.elim0
  buffer_contents := fun _ _ i => i.elim0
  availability := fun _ _ i => i.elim0
  T_init := fun _ => funext fun j => j.elim0
  T_mono := fun _ j => j.elim0
  T_capacity := fun _ _ _ k => k.elim0
  service_bound := ⟨0, fun _ _ j => j.elim0⟩
  effort_completions := fun _ _ j => j.elim0
  effort := fun _ _ j => j.elim0
  capacity := fun _ _ k => k.elim0
  completions := fun _ _ j => j.elim0

theorem marp_core : ¬ (∀
    {Xstate : Type v} [Countable Xstate] {Ω : Type u} [MeasureSpace Ω] {I J K : ℕ}
    {E : Fin I → ℝ → Ω → ℕ} {lam : Fin I → ℝ}
    {v : Fin J → ℕ → Ω → ℝ} {φ : Fin J → ℕ → Ω → Fin I → ℕ}
    {m : Fin J → ℝ} {Γ : Fin J → Fin I → ℝ} {Psi : Fin J → ℕ → Ω → ℝ × (Fin I → ℕ)}
    (ba : BaselineAssumptionsMArP I J E lam v φ m Γ Psi)
    (dat : SPNData I J K) {N0 : Fin J → ℕ} {Z0 : Fin I → ℕ}
    {S F N : ℝ → Ω → Fin J → ℕ} {T : ℝ → Ω → Fin J → ℝ} {D Z : ℝ → Ω → Fin I → ℕ}
    (M : MarkovRepresentation Xstate I J N Z)
    (hmodel : IsBasicSPN dat E v φ N0 Psi Z0 S F N T D Z ∨
      ∃ β : ℝ → Ω → Fin J → ℝ, IsRelaxedSPN dat E v φ N0 Psi Z0 S F N T D Z β ∧
        ∃ g : Xstate → Fin J → ℝ, ∀ (t : ℝ) (ω : Ω), 0 ≤ t → β t ω = g (M.X t ω))
    (hstable : IsStable M),
    lam ∈ SubcriticalRegion (SPNPlanningData.ofOutputMatrix dat.B Γ m
      (fun j => (ba.mean_service_time j).2.2) dat.A dat.b dat.b_pos)) := by
  intro h
  have ba : BaselineAssumptionsMArP (Ω := CΩ.{u}) 0 0 (fun i => i.elim0) (fun i => i.elim0)
      (fun j => j.elim0) (fun j => j.elim0) (fun j => j.elim0) (fun j => j.elim0)
      (fun j => j.elim0) :=
    { cPVA with
      arrival_nonneg := fun i => i.elim0
      arrival_slln := prob_tendsto_triv _ _ _ }
  exact not_subcrit (h ba cDat cM.{u, v} (Or.inl cBasic) cM_stable)

theorem goal_core : ¬ (∀
    {Xstate : Type v} [Countable Xstate] {Ω : Type u} [MeasureSpace Ω] {I J K : ℕ}
    {N0 : Fin J → ℕ} {E : Fin I → ℝ → Ω → ℕ} {lam : Fin I → ℝ≥0}
    {v : Fin J → ℕ → Ω → ℝ} {φ : Fin J → ℕ → Ω → Fin I → ℕ}
    {m : Fin J → ℝ} {Γ : Fin J → Fin I → ℝ} {Psi : Fin J → ℕ → Ω → ℝ × (Fin I → ℕ)}
    (ba : BaselineAssumptions I J N0 E lam v φ m Γ Psi)
    (dat : SPNData I J K) {Z0 : Fin I → ℕ}
    {S F N : ℝ → Ω → Fin J → ℕ} {T : ℝ → Ω → Fin J → ℝ} {D Z : ℝ → Ω → Fin I → ℕ}
    (M : MarkovRepresentation Xstate I J N Z)
    (hmodel : IsBasicSPN dat E v φ N0 Psi Z0 S F N T D Z ∨
      ∃ β : ℝ → Ω → Fin J → ℝ, IsRelaxedSPN dat E v φ N0 Psi Z0 S F N T D Z β ∧
        ∃ g : Xstate → Fin J → ℝ, ∀ (t : ℝ) (ω : Ω), 0 ≤ t → β t ω = g (M.X t ω))
    (hstable : IsStable M),
    (fun i => (lam i : ℝ)) ∈
      SubcriticalRegion (SPNPlanningData.ofOutputMatrix dat.B Γ m
        (fun j => (ba.mean_service_time j).2.2) dat.A dat.b dat.b_pos)) := by
  intro h
  have ba : BaselineAssumptions (Ω := CΩ.{u}) 0 0 (fun j => j.elim0) (fun i => i.elim0)
      (fun i => i.elim0) (fun j => j.elim0) (fun j => j.elim0) (fun j => j.elim0)
      (fun j => j.elim0) (fun j => j.elim0) :=
    { poisson := fun i => i.elim0
      arrivals_indep := iIndep_triv _ _ (fun i => i.elim0)
      no_arrival_iff_zero_rate := fun i => i.elim0
      processing_iid := fun j => j.elim0
      processing_positive := fun j => j.elim0
      mean_service_time := fun j => j.elim0
      mean_output := fun j => j.elim0
      phase_type := fun j => j.elim0
      mutual_independence := iIndep_triv _ _ (fun i => by
        fin_cases i <;> exact comap_subsingleton _) }
  exact not_subcrit (h ba cDat cM.{u, v} (Or.inl cBasic) cM_stable)

theorem alt_core : ¬ (∀
    {Ω : Type u} [MeasureSpace Ω] {L I J K : ℕ} {Xstate : Type v} [Countable Xstate]
    {N0 : Fin J → ℕ} {E : Fin I → ℝ → Ω → ℕ}
    {v : Fin J → ℕ → Ω → ℝ} {φ : Fin J → ℕ → Ω → Fin I → ℕ}
    {m : Fin J → ℝ} {Γ : Fin J → Fin I → ℝ} {Psi : Fin J → ℕ → Ω → ℝ × (Fin I → ℕ)}
    (pa : ProcessingVariableAssumptions I J E v φ m Γ Psi)
    (G : Matrix (Fin L) (Fin I) ℝ) (hG : ∀ ℓ i, G ℓ i = 0 ∨ G ℓ i = 1)
    (U : Fin L → ℝ → Ω → ℕ) (nu : Fin L → ℝ) (hnu : ∀ ℓ, 0 < nu ℓ)
    (hU : ℙ {ω | Filter.Tendsto (fun t : ℝ => fun ℓ => (U ℓ t ω : ℝ) / t)
        Filter.atTop (nhds nu)} = 1)
    (V : Fin L → Fin I → ℝ → Ω → ℕ)
    (hVG : ∀ ℓ i, G ℓ i = 0 → ∀ (t : ℝ) (ω : Ω), V ℓ i t ω = 0)
    (hVsum : ∀ (ℓ : Fin L) (t : ℝ) (ω : Ω), ∑ i, V ℓ i t ω = U ℓ t ω)
    (hE : ∀ (i : Fin I) (t : ℝ) (ω : Ω), E i t ω = ∑ ℓ, V ℓ i t ω)
    (dat : SPNData I J K) {Z0 : Fin I → ℕ}
    {S F N : ℝ → Ω → Fin J → ℕ} {T : ℝ → Ω → Fin J → ℝ} {D Z : ℝ → Ω → Fin I → ℕ}
    (M : MarkovRepresentation Xstate I J N Z) (hrate : ∃ C : ℝ, ∀ x, M.rate x ≤ C)
    (hVjump : ∃ g : Xstate → Xstate → Fin L → Fin I → ℕ,
      IsJumpFunctional M (fun t ω => fun ℓ i => V ℓ i t ω) g)
    (hmodel : IsBasicSPN dat E v φ N0 Psi Z0 S F N T D Z ∨
      ∃ β : ℝ → Ω → Fin J → ℝ, IsRelaxedSPN dat E v φ N0 Psi Z0 S F N T D Z β ∧
        ∃ g : Xstate → Fin J → ℝ, ∀ (t : ℝ) (ω : Ω), 0 ≤ t → β t ω = g (M.X t ω))
    (hstable : IsStable M),
    IsAugmentedSubcritical (SPNPlanningData.ofOutputMatrix dat.B Γ m
      (fun j => (pa.mean_service_time j).2.2) dat.A dat.b dat.b_pos) G nu) := by
  intro h
  exact not_aug_subcrit (h (L := 0) cPVA.{u} 0 (fun l => l.elim0) (fun l => l.elim0)
    (fun l => l.elim0) (fun l => l.elim0) (prob_tendsto_triv _ _ _) (fun l => l.elim0)
    (fun l => l.elim0) (fun l => l.elim0) (fun i => i.elim0) cDat cM.{u, v}
    ⟨1, fun _ => le_rfl⟩ ⟨fun _ _ l => l.elim0, fun _ _ _ => Subsingleton.elim _ _⟩
    (Or.inl cBasic) cM_stable)

end ProcessingNetworks.Subcriticality

open ProcessingNetworks.Subcriticality


theorem solution : ¬ (∀
    {Ω : Type} [MeasureSpace Ω] {L I J K : ℕ} {Xstate : Type} [Countable Xstate]
    {N0 : Fin J → ℕ} {E : Fin I → ℝ → Ω → ℕ}
    {v : Fin J → ℕ → Ω → ℝ} {φ : Fin J → ℕ → Ω → Fin I → ℕ}
    {m : Fin J → ℝ} {Γ : Fin J → Fin I → ℝ} {Psi : Fin J → ℕ → Ω → ℝ × (Fin I → ℕ)}
    (pa : ProcessingVariableAssumptions I J E v φ m Γ Psi)
    (G : Matrix (Fin L) (Fin I) ℝ) (hG : ∀ ℓ i, G ℓ i = 0 ∨ G ℓ i = 1)
    (U : Fin L → ℝ → Ω → ℕ) (nu : Fin L → ℝ) (hnu : ∀ ℓ, 0 < nu ℓ)
    (hU : ℙ {ω | Filter.Tendsto (fun t : ℝ => fun ℓ => (U ℓ t ω : ℝ) / t)
        Filter.atTop (nhds nu)} = 1)
    (V : Fin L → Fin I → ℝ → Ω → ℕ)
    (hVG : ∀ ℓ i, G ℓ i = 0 → ∀ (t : ℝ) (ω : Ω), V ℓ i t ω = 0)
    (hVsum : ∀ (ℓ : Fin L) (t : ℝ) (ω : Ω), ∑ i, V ℓ i t ω = U ℓ t ω)
    (hE : ∀ (i : Fin I) (t : ℝ) (ω : Ω), E i t ω = ∑ ℓ, V ℓ i t ω)
    (dat : SPNData I J K) {Z0 : Fin I → ℕ}
    {S F N : ℝ → Ω → Fin J → ℕ} {T : ℝ → Ω → Fin J → ℝ} {D Z : ℝ → Ω → Fin I → ℕ}
    (M : MarkovRepresentation Xstate I J N Z) (hrate : ∃ C : ℝ, ∀ x, M.rate x ≤ C)
    (hVjump : ∃ g : Xstate → Xstate → Fin L → Fin I → ℕ,
      IsJumpFunctional M (fun t ω => fun ℓ i => V ℓ i t ω) g)
    (hmodel : IsBasicSPN dat E v φ N0 Psi Z0 S F N T D Z ∨
      ∃ β : ℝ → Ω → Fin J → ℝ, IsRelaxedSPN dat E v φ N0 Psi Z0 S F N T D Z β ∧
        ∃ g : Xstate → Fin J → ℝ, ∀ (t : ℝ) (ω : Ω), 0 ≤ t → β t ω = g (M.X t ω))
    (hstable : IsStable M),
    IsAugmentedSubcritical (SPNPlanningData.ofOutputMatrix dat.B Γ m
      (fun j => (pa.mean_service_time j).2.2) dat.A dat.b dat.b_pos) G nu) := alt_core.{0, 0}
