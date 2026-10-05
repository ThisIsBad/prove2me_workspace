import Mathlib
import Definitions.Def_ProcessingNetworks_PacketNetworks_RPSResidualProcess
import Definitions.Def_ProcessingNetworks_PacketNetworks_RPSFluidModel

namespace ProcessingNetworks.PacketNetworks

open MeasureTheory Filter

namespace DRCE

def datc : PacketNetworkData 1 1 := ⟨fun _ => 0, fun _ => none⟩

def Sc : Finset (Fin 1 → ℕ) := {fun _ => 0, fun _ => 1}

theorem fin1_eq (s t : Fin 1 → ℕ) : s = t ↔ s 0 = t 0 := by
  constructor
  · intro h; rw [h]
  · intro h; funext i; rw [Subsingleton.elim i 0]; exact h


noncomputable def cfg2 : LinkConfigData 1 1 where
  A := fun _ _ => 1
  hA := fun j => ⟨0, rfl, fun k _ => Subsingleton.elim _ _⟩
  hA0 := fun j k h => absurd rfl h
  C := {fun _ => 0, fun _ => 1}

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

theorem psi2 (y : Fin 1 → ℝ) (hy : 0 < y 0) :
    ProportionalFairness.psi (hullFinset fr2.cfg.C) y 0 = 1 := by
  have hex : ∃ x, ProportionalFairness.IsPFMaximizer (hullFinset fr2.cfg.C) y x :=
    ⟨_, pfmax2 y (fun i => by rw [Subsingleton.elim i 0]; exact hy.le)⟩
  simp only [ProportionalFairness.psi, if_pos hy, dif_pos hex]
  have hm := Classical.choose_spec hex
  set x := Classical.choose hex
  have hx := hm.1
  rw [hull2] at hx
  have h0 : 0 ≤ x 0 := hx.1 0
  have h1 : x 0 ≤ 1 := hx.2 0
  have hle := hm.2 _ one_mem_hull2
  simp only [ProportionalFairness.f, ProportionalFairness.extLog, Fin.sum_univ_one, one_ne_zero,
    if_false, Real.log_one, EReal.coe_zero, mul_zero] at hle
  split_ifs at hle with hx0
  · exfalso
    have : (y 0 : EReal) * ⊥ = ⊥ := EReal.mul_bot_of_pos (by exact_mod_cast hy)
    rw [this] at hle
    exact absurd hle (by simp)
  · rw [← EReal.coe_mul] at hle
    have hle' : 0 ≤ y 0 * Real.log (x 0) := by exact_mod_cast hle
    have hpos : 0 < x 0 := lt_of_le_of_ne h0 (Ne.symm hx0)
    by_contra hne
    have hlt : x 0 < 1 := lt_of_le_of_ne h1 hne
    have := Real.log_neg hpos hlt
    nlinarith


/-! ## idle pattern -/

def Nn (ℓ : ℕ) : ℕ := (ℓ + 1).factorial * (ℓ + 1).factorial

theorem Nn_succ (ℓ : ℕ) : Nn (ℓ + 1) = (ℓ + 2) * (ℓ + 2) * Nn ℓ := by
  simp only [Nn, Nat.factorial_succ (ℓ + 1)]; ring

theorem Nn_pos (ℓ : ℕ) : 0 < Nn ℓ := by unfold Nn; positivity

theorem Nn_ge (ℓ : ℕ) : (ℓ + 1) * (ℓ + 1) ≤ Nn ℓ :=
  Nat.mul_le_mul (Nat.self_le_factorial _) (Nat.self_le_factorial _)

theorem Nn_mono : StrictMono Nn :=
  strictMono_nat_of_lt_succ (fun ℓ => by
    rw [Nn_succ]; have := Nn_pos ℓ
    have h4 : 4 ≤ (ℓ + 2) * (ℓ + 2) := by nlinarith
    calc Nn ℓ < 4 * Nn ℓ := by omega
      _ ≤ _ := Nat.mul_le_mul_right _ h4)

theorem Nn_two (ℓ : ℕ) : 2 * Nn ℓ ≤ Nn (ℓ + 1) := by
  rw [Nn_succ]
  have h4 : 2 ≤ (ℓ + 2) * (ℓ + 2) := by nlinarith
  exact Nat.mul_le_mul_right _ h4

def idle (m : ℕ) : Prop := ∃ ℓ < m, Nn ℓ < m ∧ m ≤ 2 * Nn ℓ

instance : DecidablePred idle := fun m => by unfold idle; infer_instance

def w (τ : ℕ) : ℕ := ((Finset.Icc 1 τ).filter idle).card

theorem w_zero : w 0 = 0 := by simp [w]

theorem w_succ (τ : ℕ) : w (τ + 1) = w τ + if idle (τ + 1) then 1 else 0 := by
  unfold w
  rw [Finset.card_filter, Finset.card_filter, Finset.sum_Icc_succ_top (by omega)]

theorem w_lower (n τ : ℕ) : min τ (2 * Nn n) - Nn n ≤ w τ := by
  have h : Finset.Ioc (Nn n) (min τ (2 * Nn n)) ⊆ (Finset.Icc 1 τ).filter idle := by
    intro m hm
    rw [Finset.mem_Ioc] at hm
    have h1 := Nn_ge n
    rw [Finset.mem_filter, Finset.mem_Icc]
    refine ⟨⟨by nlinarith, le_trans hm.2 (min_le_left _ _)⟩, n, by nlinarith, hm.1,
      le_trans hm.2 (min_le_right _ _)⟩
  have := Finset.card_le_card h
  rw [Nat.card_Ioc] at this
  exact this

theorem w_upper (n τ : ℕ) (hn : 1 ≤ n) (hτ : τ < Nn (n + 1)) :
    w τ ≤ 2 * Nn (n - 1) + (min τ (2 * Nn n) - Nn n) := by
  have h : (Finset.Icc 1 τ).filter idle ⊆
      Finset.Icc 1 (2 * Nn (n - 1)) ∪ Finset.Ioc (Nn n) (min τ (2 * Nn n)) := by
    intro m hm
    rw [Finset.mem_filter, Finset.mem_Icc] at hm
    obtain ⟨⟨hm1, hmτ⟩, ℓ, -, hl1, hl2⟩ := hm
    rw [Finset.mem_union, Finset.mem_Icc, Finset.mem_Ioc]
    rcases lt_trichotomy ℓ n with h | h | h
    · left
      refine ⟨hm1, le_trans hl2 ?_⟩
      have : Nn ℓ ≤ Nn (n - 1) := Nn_mono.monotone (by omega)
      omega
    · right; subst h; exact ⟨hl1, le_min hmτ hl2⟩
    · exfalso
      have : Nn (n + 1) ≤ Nn ℓ := Nn_mono.monotone (by omega)
      omega
  have := (Finset.card_le_card h).trans (Finset.card_union_le _ _)
  rw [Nat.card_Icc, Nat.card_Ioc] at this
  unfold w; omega


/-! ## primitives -/

noncomputable def fd (z : Fin 1 → ℕ) (u : ℝ) : Fin 1 → ℕ :=
  if 1 ≤ z 0 ∧ u ≠ 1 / 2 then fun _ => 1 else fun _ => 0

noncomputable def Pd : PacketPrimitives 1 1 Unit where
  f := fd
  Eincr _ _ := fun _ => 1
  U τ _ := if idle τ then 1 / 2 else 1 / 4

theorem state (N : ℕ) (hN : 1 ≤ N) (τ : ℕ) :
    policyState datc Pd (fun _ => N) τ () = fun _ => ((N + w τ : ℕ) : ℤ) := by
  induction τ with
  | zero => funext i; simp [policyState, w_zero]
  | succ τ ih =>
    funext i
    simp only [policyState, ih]
    have h1 : 1 ≤ N + w τ := by omega
    simp only [nextState, Rint, datc, Pd, fd, Fin.sum_univ_one, w_succ, Int.toNat_natCast]
    fin_cases i
    by_cases hi : idle (τ + 1)
    · simp [hi, h1]; ring
    · have : (1 / 4 : ℝ) ≠ 1 / 2 := by norm_num
      simp [hi, h1, this]

theorem sched (N : ℕ) (hN : 1 ≤ N) (m : ℕ) (hm : 1 ≤ m) :
    policySched datc Pd (fun _ => N) m () = fun _ => if idle m then 0 else 1 := by
  simp only [policySched, state N hN, Int.toNat_natCast]
  have h1 : 1 ≤ N + w (m - 1) := by omega
  simp only [Pd, fd]
  by_cases hi : idle m
  · simp [hi]
  · have : (1 / 4 : ℝ) ≠ 1 / 2 := by norm_num
    simp [hi, h1, this]

theorem dproc (N : ℕ) (hN : 1 ≤ N) (τ : ℕ) :
    Dproc datc Pd (fun _ => N) τ () 0 = (τ : ℝ) - (w τ : ℝ) := by
  induction τ with
  | zero => simp [Dproc, w_zero]
  | succ τ ih =>
    simp only [Dproc] at ih ⊢
    rw [Finset.sum_Icc_succ_top (by omega), ih, sched N hN (τ + 1) (by omega), w_succ]
    by_cases hi : idle (τ + 1) <;> simp [hi] <;> ring

theorem c01 : (fun _ : Fin 1 => (0:ℕ)) ≠ fun _ => 1 := by
  intro h; have := congrFun h 0; simp at this

theorem tproc1 (N : ℕ) (hN : 1 ≤ N) (τ : ℕ) :
    Tproc datc Pd (fun _ => N) (fun _ => 1) τ () = (τ : ℝ) - (w τ : ℝ) := by
  induction τ with
  | zero => simp [Tproc, w_zero]
  | succ τ ih =>
    simp only [Tproc] at ih ⊢
    rw [Finset.card_filter, Finset.sum_Icc_succ_top (by omega), ← Finset.card_filter]
    push_cast
    rw [ih, sched N hN (τ + 1) (by omega), w_succ]
    by_cases hi : idle (τ + 1) <;> simp [hi, c01] <;> ring

theorem tproc0 (N : ℕ) (hN : 1 ≤ N) (τ : ℕ) :
    Tproc datc Pd (fun _ => N) (fun _ => 0) τ () = (w τ : ℝ) := by
  induction τ with
  | zero => simp [Tproc, w_zero]
  | succ τ ih =>
    simp only [Tproc] at ih ⊢
    rw [Finset.card_filter, Finset.sum_Icc_succ_top (by omega), ← Finset.card_filter]
    push_cast
    rw [ih, sched N hN (τ + 1) (by omega), w_succ]
    by_cases hi : idle (τ + 1) <;> simp [hi, c01.symm]

theorem integ (M : ℕ) (hM : 1 ≤ M) :
    ∫ uu in Set.Ioo (0 : ℝ) 1, ((fd (fun _ => M) uu 0 : ℕ) : ℝ) = 1 := by
  have hae : (fun u : ℝ => ((fd (fun _ => M) u 0 : ℕ) : ℝ)) =ᵐ[volume.restrict (Set.Ioo (0:ℝ) 1)]
      fun _ => 1 := by
    apply ae_restrict_of_ae
    have : ∀ᵐ u ∂(volume : Measure ℝ), u ≠ 1 / 2 := by
      rw [ae_iff]; simp
    filter_upwards [this] with u hu
    have hu' : ¬ u = 2⁻¹ := by rw [← one_div]; exact hu
    simp [fd, hM, hu']
  rw [integral_congr_ae hae]
  simp [Real.volume_Ioo]

theorem xi_eq (N : ℕ) (hN : 1 ≤ N) (τ : ℕ) :
    xi fr2 Pd (fun _ => N) 0 τ () = - (w τ : ℝ) := by
  have hs : ∀ m ∈ Finset.Icc 1 τ, shat fr2 Pd (fun _ => N) 0 m () = 1 := by
    intro m hm
    unfold shat
    have : fr2.dat = datc := rfl
    rw [this, state N hN]
    simp only [Int.toNat_natCast]
    exact integ _ (by omega)
  unfold xi
  rw [Finset.sum_congr rfl (fun m hm => by rw [hs m hm]), Finset.sum_sub_distrib]
  have hD := dproc N hN τ
  simp only [Dproc] at hD
  have : fr2.dat = datc := rfl
  rw [this, hD]
  simp


theorem hRPSd : IsRPSPolicy fr2 Sc Pd.f := by
  refine ⟨?_, fun _ _ => fun _ => 1, fun _ => measurable_const, ?_, ?_, ?_⟩
  · intro z u _ _
    refine ⟨?_, fun i => ?_⟩
    · simp only [Pd, fd, Sc]; split_ifs <;> simp
    · rw [Subsingleton.elim i 0]
      simp only [B, fr2, datc, Pd, fd, Matrix.mulVec, dotProduct]
      by_cases h : 1 ≤ z 0 ∧ u ≠ 1 / 2
      · simp only [if_pos h]
        simp only [Fin.sum_univ_one, if_true, one_mul, Nat.cast_one]
        exact_mod_cast h.1
      · simp only [if_neg h]
        simp
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
          have hset : {uu : ℝ | uu ∈ Set.Ioo 0 1 ∧ Pd.f z uu = fun _ => 1} =
              Set.Ioo 0 1 \ {1 / 2} := by
            ext u
            simp only [Set.mem_setOf_eq, Set.mem_diff, Set.mem_singleton_iff, Pd, fd]
            by_cases hu : u = 1 / 2
            · simp [hu, c01]
            · have hu' : ¬ u = 2⁻¹ := by rw [← one_div]; exact hu
              simp [hu', hz]
          rw [hset, measure_sdiff_null (measure_singleton _)]
          have : ((z 0 : ℕ) : ℝ) ≠ 0 := by
            have : 0 < z 0 := by omega
            exact_mod_cast this.ne'
          simp [this, Real.volume_Ioo]
        · have hsub : {uu : ℝ | uu ∈ Set.Ioo 0 1 ∧ Pd.f z uu = s} ⊆ {1 / 2} := by
            intro u hu
            simp only [Set.mem_setOf_eq, Pd, fd] at hu
            by_contra hne
            rw [Set.mem_singleton_iff] at hne
            rw [if_pos ⟨hz, hne⟩] at hu
            exact hs (by rw [← hu.2])
          rw [measure_mono_null hsub (measure_singleton _)]
          simp [hs]
      · have hz0 : z 0 = 0 := by omega
        have hm : min 1 (z 0) = 0 := by rw [hz0]; rfl
        rw [hm]
        have hf : ∀ uu, Pd.f z uu = fun _ => 0 := by
          intro uu; simp [Pd, fd, hz]
        by_cases hs : s 0 = 0
        · have hs' : s = fun _ => 0 := by funext i; rw [Subsingleton.elim i 0, hs]
          subst hs'
          simp [hf]
          show volume (Set.Ioo (0:ℝ) 1) = 1
          simp [Real.volume_Ioo]
        · have : ∀ uu, Pd.f z uu ≠ s := by
            intro uu h; apply hs; rw [← h, hf]
          simp [this, hs]

theorem slln : SLLNHoldsAt Pd (fun _ => 1) () := by
  intro M hM ε hε
  refine ⟨2 / ε, fun size hs t ht i => ?_⟩
  have hsz : 0 < size := lt_of_lt_of_le (by positivity) hs
  have hE : (Ecum Pd ⌊size * t⌋₊ () i : ℝ) = ⌊size * t⌋₊ := by simp [Ecum, Pd]
  rw [hE]
  have h0 : 0 ≤ size * t := mul_nonneg hsz.le ht.1
  have f1 := Nat.floor_le h0
  have f2 := Nat.lt_floor_add_one (size * t)
  have key : size⁻¹ * (⌊size * t⌋₊ : ℝ) - 1 * t = ((⌊size * t⌋₊ : ℝ) - size * t) / size := by
    field_simp
  rw [key, abs_div, abs_of_pos hsz, div_lt_iff₀ hsz]
  have h1 : |(⌊size * t⌋₊ : ℝ) - size * t| < 1 := by rw [abs_lt]; constructor <;> linarith
  have h2 : 2 ≤ ε * size := by rw [div_le_iff₀ hε] at hs; linarith
  linarith

noncomputable def v (t : ℝ) : ℝ := min (max (t - 1) 0) 1

theorem v_lip (a b : ℝ) : |v a - v b| ≤ |a - b| := by
  have h1 := abs_min_sub_min_le_max (max (a - 1) 0) 1 (max (b - 1) 0) 1
  have h2 := abs_max_sub_max_le_abs (a - 1) (b - 1) 0
  simp only [sub_self, abs_zero, max_eq_left (abs_nonneg (max (a - 1) 0 - max (b - 1) 0))] at h1
  unfold v
  rw [show a - b = (a - 1) - (b - 1) by ring]
  linarith

theorem cnat (N τ : ℕ) (hN : 0 < N) :
    ((min τ (2 * N) - N : ℕ) : ℝ) = N * v (τ / N) := by
  have hNr : (0:ℝ) < N := by exact_mod_cast hN
  unfold v
  rcases le_total τ N with h | h
  · rw [Nat.sub_eq_zero_of_le (le_trans (min_le_left _ _) h)]
    have : (τ:ℝ) / N ≤ 1 := by rw [div_le_one hNr]; exact_mod_cast h
    rw [max_eq_right (by linarith), min_eq_left zero_le_one]; simp
  · rcases le_total τ (2 * N) with h2 | h2
    · rw [min_eq_left h2, Nat.cast_sub h]
      have a1 : 1 ≤ (τ:ℝ) / N := by rw [le_div_iff₀ hNr]; simp; exact_mod_cast h
      have a2 : (τ:ℝ) / N ≤ 2 := by rw [div_le_iff₀ hNr]; exact_mod_cast h2
      rw [max_eq_left (by linarith), min_eq_left (by linarith)]
      field_simp
    · rw [min_eq_right h2, show 2 * N - N = N by omega]
      have a2 : 2 ≤ (τ:ℝ) / N := by rw [le_div_iff₀ hNr]; exact_mod_cast (by linarith : 2 * N ≤ τ)
      rw [max_eq_left (by linarith), min_eq_right (by linarith)]; ring


theorem KE (Tb : ℝ) (ε : ℝ) (hε : 0 < ε) : ∃ L : ℕ, ∀ n ≥ L, ∀ t ∈ Set.Icc (0:ℝ) Tb,
    |(Nn n : ℝ)⁻¹ * (w ⌊(Nn n : ℝ) * t⌋₊ : ℝ) - v t| < ε ∧
    |(Nn n : ℝ)⁻¹ * (⌊(Nn n : ℝ) * t⌋₊ : ℝ) - t| < ε := by
  refine ⟨⌈Tb⌉₊ + ⌈3 / ε⌉₊ + 1, fun n hn t ht => ?_⟩
  have hn1 : 1 ≤ n := by omega
  have hnT : Tb ≤ n := le_trans (Nat.le_ceil Tb) (by exact_mod_cast (by omega : ⌈Tb⌉₊ ≤ n))
  have hnε : 3 / ε < (n:ℝ) + 1 :=
    lt_of_le_of_lt (Nat.le_ceil _) (by exact_mod_cast (by omega : ⌈3 / ε⌉₊ < n + 1))
  have hNpos : (0:ℝ) < Nn n := by exact_mod_cast Nn_pos n
  have hNge : ((n:ℝ) + 1) * ((n:ℝ) + 1) ≤ Nn n := by exact_mod_cast Nn_ge n
  have hrec : (Nn n : ℝ) = ((n:ℝ) + 1) * ((n:ℝ) + 1) * Nn (n - 1) := by
    have := Nn_succ (n - 1)
    rw [show n - 1 + 1 = n by omega] at this
    rw [this]; push_cast; rw [Nat.cast_sub hn1]; ring
  have h0 : 0 ≤ (Nn n : ℝ) * t := mul_nonneg hNpos.le ht.1
  have f1 : (⌊(Nn n : ℝ) * t⌋₊ : ℝ) ≤ Nn n * t := Nat.floor_le h0
  have f2 : (Nn n : ℝ) * t < ⌊(Nn n : ℝ) * t⌋₊ + 1 := Nat.lt_floor_add_one _
  have hτlt : ⌊(Nn n : ℝ) * t⌋₊ < Nn (n + 1) := by
    have : (⌊(Nn n : ℝ) * t⌋₊ : ℝ) < Nn (n + 1) := by
      rw [Nn_succ]; push_cast
      calc (⌊(Nn n : ℝ) * t⌋₊ : ℝ) ≤ Nn n * t := f1
        _ ≤ Nn n * n := mul_le_mul_of_nonneg_left (le_trans ht.2 hnT) hNpos.le
        _ < ((n:ℝ) + 2) * ((n:ℝ) + 2) * Nn n := by nlinarith
    exact_mod_cast this
  have hlo := w_lower n ⌊(Nn n : ℝ) * t⌋₊
  have hup := w_upper n ⌊(Nn n : ℝ) * t⌋₊ hn1 hτlt
  have hc := cnat (Nn n) ⌊(Nn n : ℝ) * t⌋₊ (Nn_pos n)
  generalize ⌊(Nn n : ℝ) * t⌋₊ = τ at *
  generalize hcdef : min τ (2 * Nn n) - Nn n = c at *
  generalize hW : w τ = W at *
  have hlo' : (c:ℝ) ≤ W := by exact_mod_cast hlo
  have hup' : (W : ℝ) ≤ 2 * Nn (n - 1) + c := by exact_mod_cast hup
  have hinv : (Nn n : ℝ)⁻¹ ≤ 1 / ((n:ℝ) + 1) := by
    rw [inv_eq_one_div]
    apply one_div_le_one_div_of_le (by positivity)
    nlinarith
  have hε3 : 3 / ((n:ℝ) + 1) < ε := by
    rw [div_lt_iff₀ (by positivity)]; rw [div_lt_iff₀ hε] at hnε; linarith
  have hE1 : |(Nn n : ℝ)⁻¹ * τ - t| ≤ 1 / ((n:ℝ) + 1) := by
    rw [show (Nn n : ℝ)⁻¹ * τ - t = (Nn n : ℝ)⁻¹ * (τ - Nn n * t) by field_simp]
    rw [abs_mul, abs_of_pos (inv_pos.mpr hNpos)]
    have : |(τ:ℝ) - Nn n * t| ≤ 1 := by rw [abs_le]; constructor <;> linarith
    calc (Nn n : ℝ)⁻¹ * |(τ:ℝ) - Nn n * t| ≤ (Nn n : ℝ)⁻¹ * 1 :=
          mul_le_mul_of_nonneg_left this (inv_nonneg.mpr hNpos.le)
      _ ≤ _ := by rw [mul_one]; exact hinv
  have hvc : (Nn n : ℝ)⁻¹ * c = v (τ / Nn n) := by
    rw [hc]; field_simp
  have hv := v_lip (τ / Nn n) t
  rw [show (τ:ℝ) / Nn n = (Nn n : ℝ)⁻¹ * τ by ring] at hv hvc
  have hgap : (Nn n : ℝ)⁻¹ * (2 * Nn (n - 1)) ≤ 2 / ((n:ℝ) + 1) := by
    rw [hrec]
    have hp : (0:ℝ) < Nn (n - 1) := by exact_mod_cast Nn_pos (n - 1)
    rw [mul_inv, mul_inv]
    have e : ((n:ℝ) + 1)⁻¹ * ((n:ℝ) + 1)⁻¹ * (Nn (n - 1) : ℝ)⁻¹ * (2 * Nn (n - 1)) =
        2 / ((n:ℝ) + 1) * ((n:ℝ) + 1)⁻¹ := by field_simp
    rw [e]
    have : ((n:ℝ) + 1)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith)
    have : 0 ≤ 2 / ((n:ℝ) + 1) := by positivity
    nlinarith
  constructor
  · have hA : 0 ≤ (Nn n : ℝ)⁻¹ * W - (Nn n : ℝ)⁻¹ * c := by
      rw [← mul_sub]; exact mul_nonneg (inv_nonneg.mpr hNpos.le) (by linarith)
    have hB : (Nn n : ℝ)⁻¹ * W - (Nn n : ℝ)⁻¹ * c ≤ 2 / ((n:ℝ) + 1) := by
      rw [← mul_sub]
      calc (Nn n : ℝ)⁻¹ * (W - c) ≤ (Nn n : ℝ)⁻¹ * (2 * Nn (n - 1)) :=
            mul_le_mul_of_nonneg_left (by linarith) (inv_nonneg.mpr hNpos.le)
        _ ≤ _ := hgap
    rw [hvc] at hA hB
    have := abs_sub_le ((Nn n : ℝ)⁻¹ * W) (v ((Nn n : ℝ)⁻¹ * τ)) (v t)
    rw [abs_of_nonneg hA] at this
    have h13 : 1 / ((n:ℝ) + 1) + 2 / ((n:ℝ) + 1) = 3 / ((n:ℝ) + 1) := by ring
    linarith
  · have h13 : 1 / ((n:ℝ) + 1) < 3 / ((n:ℝ) + 1) := by
      apply div_lt_div_of_pos_right (by norm_num) (by positivity)
    linarith


def zs (ℓ : ℕ) : Fin 1 → ℕ := fun _ => Nn ℓ

theorem size_zs (ℓ : ℕ) : sizeN (zs ℓ) = Nn ℓ := by simp [sizeN, zs]

theorem hzs : ∀ ℓ : ℕ, ((ℓ : ℝ) + 1) ^ 2 ≤ sizeN (zs ℓ) := by
  intro ℓ; rw [size_zs, sq]; exact_mod_cast Nn_ge ℓ

noncomputable def Dhd (t : ℝ) : Fin 1 → ℝ := fun _ => t - v t
noncomputable def Zhd (t : ℝ) : Fin 1 → ℝ := fun _ => 1 + v t
noncomputable def Thd (t : ℝ) (s : Fin 1 → ℕ) : ℝ :=
  if s = (fun _ => 1) then t - v t else if s = (fun _ => 0) then v t else 0

theorem conv : FluidScaledConverge fr2.dat Pd Sc () zs Dhd Thd Zhd := by
  refine ⟨?_, ?_, ?_⟩
  · intro Tb hTb ε hε
    obtain ⟨L, hL⟩ := KE Tb (ε / 2) (by positivity)
    refine ⟨L, fun n hn t ht i => ?_⟩
    obtain ⟨h1, h2⟩ := hL n hn t ht
    fin_cases i
    simp only [size_zs]
    show |(Nn n : ℝ)⁻¹ * Dproc datc Pd (fun _ => Nn n) ⌊(Nn n : ℝ) * t⌋₊ () 0 - (t - v t)| < ε
    rw [dproc _ (Nn_pos n)]
    rw [show (Nn n : ℝ)⁻¹ * ((⌊(Nn n : ℝ) * t⌋₊ : ℝ) - (w ⌊(Nn n : ℝ) * t⌋₊ : ℝ)) - (t - v t) =
      ((Nn n : ℝ)⁻¹ * (⌊(Nn n : ℝ) * t⌋₊ : ℝ) - t) -
        ((Nn n : ℝ)⁻¹ * (w ⌊(Nn n : ℝ) * t⌋₊ : ℝ) - v t) by ring]
    have := abs_sub ((Nn n : ℝ)⁻¹ * (⌊(Nn n : ℝ) * t⌋₊ : ℝ) - t)
      ((Nn n : ℝ)⁻¹ * (w ⌊(Nn n : ℝ) * t⌋₊ : ℝ) - v t)
    linarith
  · intro Tb hTb ε hε
    obtain ⟨L, hL⟩ := KE Tb (ε / 2) (by positivity)
    refine ⟨L, fun n hn t ht s hs => ?_⟩
    obtain ⟨h1, h2⟩ := hL n hn t ht
    simp only [Sc, Finset.mem_insert, Finset.mem_singleton] at hs
    simp only [size_zs]
    rcases hs with rfl | rfl
    · show |(Nn n : ℝ)⁻¹ * Tproc datc Pd (fun _ => Nn n) (fun _ => 0) ⌊(Nn n : ℝ) * t⌋₊ () -
        Thd t (fun _ => 0)| < ε
      rw [tproc0 _ (Nn_pos n)]
      simp only [Thd, if_neg c01, if_true]
      linarith
    · show |(Nn n : ℝ)⁻¹ * Tproc datc Pd (fun _ => Nn n) (fun _ => 1) ⌊(Nn n : ℝ) * t⌋₊ () -
        Thd t (fun _ => 1)| < ε
      rw [tproc1 _ (Nn_pos n)]
      simp only [Thd, if_true]
      rw [show (Nn n : ℝ)⁻¹ * ((⌊(Nn n : ℝ) * t⌋₊ : ℝ) - (w ⌊(Nn n : ℝ) * t⌋₊ : ℝ)) - (t - v t) =
        ((Nn n : ℝ)⁻¹ * (⌊(Nn n : ℝ) * t⌋₊ : ℝ) - t) -
          ((Nn n : ℝ)⁻¹ * (w ⌊(Nn n : ℝ) * t⌋₊ : ℝ) - v t) by ring]
      have := abs_sub ((Nn n : ℝ)⁻¹ * (⌊(Nn n : ℝ) * t⌋₊ : ℝ) - t)
        ((Nn n : ℝ)⁻¹ * (w ⌊(Nn n : ℝ) * t⌋₊ : ℝ) - v t)
      linarith
  · intro Tb hTb ε hε
    obtain ⟨L, hL⟩ := KE Tb ε hε
    refine ⟨L, fun n hn t ht i => ?_⟩
    obtain ⟨h1, h2⟩ := hL n hn t ht
    fin_cases i
    simp only [size_zs]
    show |(Nn n : ℝ)⁻¹ * Zproc datc Pd (fun _ => Nn n) ⌊(Nn n : ℝ) * t⌋₊ () 0 - (1 + v t)| < ε
    simp only [Zproc, state _ (Nn_pos n)]
    have hNpos : (0:ℝ) < Nn n := by exact_mod_cast Nn_pos n
    push_cast
    rw [show (Nn n : ℝ)⁻¹ * ((Nn n : ℝ) + (w ⌊(Nn n : ℝ) * t⌋₊ : ℝ)) - (1 + v t) =
      (Nn n : ℝ)⁻¹ * (w ⌊(Nn n : ℝ) * t⌋₊ : ℝ) - v t by field_simp; ring]
    exact h1

theorem om2 : () ∈ omega2 fr2 Pd zs := by
  intro i
  fin_cases i
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨L, hL⟩ := KE 1 ε hε
  refine ⟨L, fun n hn => ?_⟩
  have h1 := (hL n hn 1 ⟨zero_le_one, le_rfl⟩).1
  simp only [mul_one, Nat.floor_natCast] at h1
  have hv1 : v 1 = 0 := by simp [v]
  rw [hv1, sub_zero] at h1
  simp only [size_zs, Nat.floor_natCast, Real.dist_eq, sub_zero]
  show |xi fr2 Pd (fun _ => Nn n) 0 (Nn n) () / (Nn n : ℝ)| < ε
  rw [xi_eq _ (Nn_pos n)]
  rw [neg_div, abs_neg, div_eq_inv_mul]
  exact h1

theorem not_eq : ¬ SatisfiesRPSFluidEquation fr2 Dhd Zhd := by
  intro hrps
  have hZt : 0 < Zhd (3 / 2) 0 := by
    simp only [Zhd, v]; norm_num
  have := hrps (3 / 2) (by norm_num) 0 hZt
  have hga : ProportionalFairness.groupAggregate fr2.linkDesig (Zhd (3 / 2)) (fr2.linkDesig 0) =
      Zhd (3 / 2) 0 := by
    simp [ProportionalFairness.groupAggregate, fr2]
  rw [hga, div_self hZt.ne', one_mul] at this
  have hg : (fun k => ProportionalFairness.groupAggregate fr2.linkDesig (Zhd (3 / 2)) k) =
      fun _ => Zhd (3 / 2) 0 := by
    funext k
    rw [Subsingleton.elim k (fr2.linkDesig 0), hga]
  have hfl : fr2.linkDesig 0 = 0 := rfl
  rw [show ProportionalFairness.groupAggregate fr2.linkDesig (Zhd (3 / 2)) =
      fun _ => Zhd (3 / 2) 0 from hg, hfl, psi2 (fun _ => Zhd (3 / 2) 0) hZt] at this
  have h2 : HasDerivAt (fun u => Dhd u 0) 0 (3 / 2) := by
    apply (hasDerivAt_const (3 / 2 : ℝ) (1 : ℝ)).congr_of_eventuallyEq
    have : Set.Ioo (1 : ℝ) 2 ∈ nhds (3 / 2 : ℝ) := Ioo_mem_nhds (by norm_num) (by norm_num)
    filter_upwards [this] with u hu
    simp only [Dhd, v]
    rw [max_eq_left (by linarith [hu.1]), min_eq_left (by linarith [hu.2])]
    ring
  have := this.unique h2
  norm_num at this

end DRCE

theorem rps_drift_false : ¬ (∀ {I K : ℕ} {Ω : Type} (fr : FixedRoutingData I K) (S : Finset (Fin I → ℕ))
    (hS : IsScheduleSet fr.cfg S) (lam : Fin I → ℝ) (P : PacketPrimitives I I Ω)
    (hRPS : IsRPSPolicy fr S P.f)
    (zseq : ℕ → Fin I → ℕ) (hzseq : ∀ ℓ : ℕ, ((ℓ : ℝ) + 1) ^ 2 ≤ sizeN (zseq ℓ))
    (ω : Ω) (hω1 : SLLNHoldsAt P lam ω) (hω2 : ω ∈ omega2 fr P zseq)
    (Dh : ℝ → Fin I → ℝ) (Th : ℝ → (Fin I → ℕ) → ℝ) (Zh : ℝ → Fin I → ℝ)
    (hlim : FluidScaledConverge fr.dat P S ω zseq Dh Th Zh),
    SatisfiesRPSFluidEquation fr Dh Zh) := by
  intro h
  exact DRCE.not_eq (h DRCE.fr2 DRCE.Sc DRCE.hS2 (fun _ => 1) DRCE.Pd DRCE.hRPSd DRCE.zs DRCE.hzs
    () DRCE.slln DRCE.om2 DRCE.Dhd DRCE.Thd DRCE.Zhd DRCE.conv)

end ProcessingNetworks.PacketNetworks

open ProcessingNetworks ProcessingNetworks.PacketNetworks MeasureTheory ProbabilityTheory

theorem solution : ¬ (∀ {I K : ℕ} {Ω : Type} (fr : FixedRoutingData I K) (S : Finset (Fin I → ℕ))
    (hS : IsScheduleSet fr.cfg S) (lam : Fin I → ℝ) (P : PacketPrimitives I I Ω)
    (hRPS : IsRPSPolicy fr S P.f)
    (zseq : ℕ → Fin I → ℕ) (hzseq : ∀ ℓ : ℕ, ((ℓ : ℝ) + 1) ^ 2 ≤ sizeN (zseq ℓ))
    (ω : Ω) (hω1 : SLLNHoldsAt P lam ω) (hω2 : ω ∈ omega2 fr P zseq)
    (Dh : ℝ → Fin I → ℝ) (Th : ℝ → (Fin I → ℕ) → ℝ) (Zh : ℝ → Fin I → ℝ)
    (hlim : FluidScaledConverge fr.dat P S ω zseq Dh Th Zh),
    SatisfiesRPSFluidEquation fr Dh Zh) :=
  ProcessingNetworks.PacketNetworks.rps_drift_false
