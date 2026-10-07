import Mathlib
import Definitions.Def_Komlos_RandomSignModel
import Definitions.Def_TalagrandConc_BanachSums_Basic

open MeasureTheory
open scoped ENNReal
open Classical

namespace TalagrandConc.BanachSums

/-! ### Calculus lemmas -/

lemma exp_le_poly4 {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    Real.exp x ≤ 1 + x + x ^ 2 / 2 + x ^ 3 / 6 + 5 * x ^ 4 / 96 := by
  have h := Real.exp_bound (x := x) (by rw [abs_of_nonneg hx0]; exact hx1) (n := 4) (by norm_num)
  rw [abs_of_nonneg hx0] at h
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at h
  have h2 := (abs_le.mp h).2
  norm_num at h2
  nlinarith [h2]

lemma exp_neg_le_poly4 {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    Real.exp (-s) ≤ 1 - s + s ^ 2 / 2 - s ^ 3 / 6 + 5 * s ^ 4 / 96 := by
  have h := Real.exp_bound (x := -s) (by rw [abs_neg, abs_of_nonneg hs0]; exact hs1) (n := 4) (by norm_num)
  rw [abs_neg, abs_of_nonneg hs0] at h
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at h
  have h2 := (abs_le.mp h).2
  norm_num at h2
  nlinarith [h2]

lemma exp_quarter_lt : Real.exp (1/4) < 1.3 := by
  have h := exp_le_poly4 (x := 1/4) (by norm_num) (by norm_num)
  norm_num at h ⊢; linarith

lemma exp_neg_half_lt : Real.exp (-(1/2)) < 0.61 := by
  have h := exp_neg_le_poly4 (s := 1/2) (by norm_num) (by norm_num)
  norm_num at h ⊢; linarith

/-- The key one–variable inequality: `e^{s-s²} + e^{-s} ≤ 2` on `[0,1/2]`. -/
lemma two_exp_le {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1/2) :
    Real.exp (s - s ^ 2) + Real.exp (-s) ≤ 2 := by
  have hx0 : 0 ≤ s - s ^ 2 := by nlinarith
  have hx1 : s - s ^ 2 ≤ 1 := by nlinarith
  have h1 := exp_le_poly4 hx0 hx1
  have h2 := exp_neg_le_poly4 hs0 (by linarith)
  have h3 : (s - s ^ 2) ^ 4 ≤ s ^ 4 := by
    have : 0 ≤ s - s^2 := hx0
    have : s - s^2 ≤ s := by nlinarith
    exact pow_le_pow_left₀ hx0 this 4
  nlinarith [pow_nonneg hs0 3, pow_nonneg hs0 4, pow_nonneg hs0 5, pow_nonneg hs0 6, mul_nonneg (pow_nonneg hs0 3) (by linarith : (0:ℝ) ≤ 1/2 - s)]

/-- Talagrand's lemma: for `0 < g ≤ 1` there is `λ ∈ [0,1]` with
`exp((1-λ)²/4) ≤ (2 - g) g^λ`. -/
lemma talagrand_key {g : ℝ} (hg0 : 0 < g) (hg1 : g ≤ 1) :
    ∃ l : ℝ, 0 ≤ l ∧ l ≤ 1 ∧ Real.exp ((1 - l) ^ 2 / 4) ≤ (2 - g) * g ^ l := by
  by_cases hg : g ≤ Real.exp (-(1/2))
  · refine ⟨0, le_rfl, zero_le_one, ?_⟩
    rw [Real.rpow_zero, mul_one]
    have := exp_quarter_lt; have := exp_neg_half_lt
    norm_num at *; linarith
  · push_neg at hg
    set s := - Real.log g with hs
    have hlog : Real.log g = -s := by rw [hs]; ring
    have hs0 : 0 ≤ s := by rw [hs]; linarith [Real.log_nonpos hg0.le hg1]
    have hs1 : s ≤ 1/2 := by
      rw [hs]
      have := Real.log_lt_log (Real.exp_pos _) hg
      rw [Real.log_exp] at this; linarith
    refine ⟨1 - 2 * s, by linarith, by linarith, ?_⟩
    have hgs : g = Real.exp (-s) := by rw [← hlog, Real.exp_log hg0]
    rw [Real.rpow_def_of_pos hg0, hlog]
    have key := two_exp_le hs0 hs1
    rw [hgs]
    have e1 : (1 - (1 - 2 * s)) ^ 2 / 4 = (s - s ^ 2) + (-s * (1 - 2 * s)) := by ring
    rw [e1, Real.exp_add]
    have hpos : 0 < Real.exp (-s * (1 - 2 * s)) := Real.exp_pos _
    have k2 : Real.exp (s - s ^ 2) ≤ 2 - Real.exp (-s) := by linarith
    exact mul_le_mul_of_nonneg_right k2 hpos.le


/-- Hölder-type inequality for finite sums via weighted AM–GM. -/
lemma holder_pt {a b F G l : ℝ} (ha : 0 < a) (hb : 0 < b) (hF : 0 < F) (hG : 0 < G)
    (h0 : 0 ≤ l) (h1 : l ≤ 1) :
    a ^ l * b ^ (1 - l) ≤ F ^ l * G ^ (1 - l) * (l * (a / F) + (1 - l) * (b / G)) := by
  have h := Real.geom_mean_le_arith_mean2_weighted (w₁ := l) (w₂ := 1 - l) (p₁ := a / F) (p₂ := b / G)
    h0 (by linarith) (div_nonneg ha.le hF.le) (div_nonneg hb.le hG.le) (by ring)
  have e : (a / F) ^ l * (b / G) ^ (1 - l) = a ^ l * b ^ (1 - l) / (F ^ l * G ^ (1 - l)) := by
    rw [Real.div_rpow ha.le hF.le, Real.div_rpow hb.le hG.le]; field_simp
  rw [e, div_le_iff₀ (by positivity)] at h
  linarith

lemma holder_sum {ι : Type*} [Fintype ι] (f g : ι → ℝ) (hf : ∀ i, 0 < f i) (hg : ∀ i, 0 < g i)
    (l : ℝ) (h0 : 0 ≤ l) (h1 : l ≤ 1) :
    ∑ i, f i ^ l * g i ^ (1 - l) ≤ (∑ i, f i) ^ l * (∑ i, g i) ^ (1 - l) := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · simp
    positivity
  have hF : 0 < ∑ i, f i := Finset.sum_pos (fun i _ => hf i) Finset.univ_nonempty
  have hG : 0 < ∑ i, g i := Finset.sum_pos (fun i _ => hg i) Finset.univ_nonempty
  calc ∑ i, f i ^ l * g i ^ (1 - l)
      ≤ ∑ i, (∑ j, f j) ^ l * (∑ j, g j) ^ (1 - l) * (l * (f i / ∑ j, f j) + (1 - l) * (g i / ∑ j, g j)) :=
        Finset.sum_le_sum (fun i _ => holder_pt (hf i) (hg i) hF hG h0 h1)
    _ = (∑ j, f j) ^ l * (∑ j, g j) ^ (1 - l) * (l * ((∑ j, f j) / ∑ j, f j) + (1 - l) * ((∑ j, g j) / ∑ j, g j)) := by
        rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
          ← Finset.sum_div, ← Finset.sum_div]
    _ = (∑ j, f j) ^ l * (∑ j, g j) ^ (1 - l) := by
        rw [div_self hF.ne', div_self hG.ne']; ring

/-! ### Convex distance on the discrete cube -/

/-- disagreement indicator -/
def dis {N : ℕ} (x y : Fin N → Bool) (i : Fin N) : ℝ := if x i = y i then 0 else 1

lemma dis_nonneg {N : ℕ} (x y : Fin N → Bool) (i : Fin N) : 0 ≤ dis x y i := by
  unfold dis; split_ifs <;> norm_num

lemma dis_le_one {N : ℕ} (x y : Fin N → Bool) (i : Fin N) : dis x y i ≤ 1 := by
  unfold dis; split_ifs <;> norm_num

/-- weighted Hamming distance from `x` to the finite set `A` -/
noncomputable def hamW {N : ℕ} (A : Finset (Fin N → Bool)) (α : Fin N → ℝ) (x : Fin N → Bool) : ℝ :=
  ⨅ y : A, ∑ i, α i * dis x y.1 i

/-- admissible weight vectors: nonnegative, Euclidean norm at most one -/
def Adm (N : ℕ) : Set (Fin N → ℝ) := {α | (∀ i, 0 ≤ α i) ∧ ∑ i, α i ^ 2 ≤ 1}

lemma zero_mem_Adm (N : ℕ) : (0 : Fin N → ℝ) ∈ Adm N := by
  refine ⟨fun i => le_rfl, ?_⟩; simp

instance (N : ℕ) : Nonempty (Adm N) := ⟨⟨0, zero_mem_Adm N⟩⟩

/-- Talagrand's convex distance (variational form) -/
noncomputable def dc {N : ℕ} (A : Finset (Fin N → Bool)) (x : Fin N → Bool) : ℝ :=
  ⨆ α : Adm N, hamW A α.1 x

lemma hamW_le {N : ℕ} (A : Finset (Fin N → Bool)) (α : Fin N → ℝ) (x : Fin N → Bool)
    {y : Fin N → Bool} (hy : y ∈ A) : hamW A α x ≤ ∑ i, α i * dis x y i := by
  unfold hamW
  exact ciInf_le (Set.finite_range _).bddBelow (⟨y, hy⟩ : A)

lemma le_hamW {N : ℕ} (A : Finset (Fin N → Bool)) (hA : A.Nonempty) (α : Fin N → ℝ) (x : Fin N → Bool)
    {c : ℝ} (h : ∀ y ∈ A, c ≤ ∑ i, α i * dis x y i) : c ≤ hamW A α x := by
  unfold hamW
  haveI : Nonempty A := ⟨⟨hA.choose, hA.choose_spec⟩⟩
  exact le_ciInf (fun y => h y.1 y.2)

lemma hamW_nonneg {N : ℕ} (A : Finset (Fin N → Bool)) (hA : A.Nonempty) {α : Fin N → ℝ}
    (hα : ∀ i, 0 ≤ α i) (x : Fin N → Bool) : 0 ≤ hamW A α x :=
  le_hamW A hA α x (fun y _ => Finset.sum_nonneg (fun i _ => mul_nonneg (hα i) (dis_nonneg _ _ _)))

lemma hamW_zero {N : ℕ} (A : Finset (Fin N → Bool)) (hA : A.Nonempty) (x : Fin N → Bool) :
    hamW A 0 x = 0 := by
  unfold hamW
  haveI : Nonempty A := ⟨⟨hA.choose, hA.choose_spec⟩⟩
  simp

lemma hamW_le_card {N : ℕ} (A : Finset (Fin N → Bool)) {α : Fin N → ℝ} (hα : α ∈ Adm N)
    (x : Fin N → Bool) : hamW A α x ≤ N := by
  rcases A.eq_empty_or_nonempty with h | h
  · subst h; unfold hamW; simp
  obtain ⟨y, hy⟩ := h
  refine (hamW_le A α x hy).trans ?_
  have h1 : ∀ i, α i ≤ 1 := by
    intro i
    have : α i ^ 2 ≤ 1 := le_trans (Finset.single_le_sum (fun j _ => sq_nonneg (α j)) (Finset.mem_univ i)) hα.2
    nlinarith [hα.1 i]
  calc ∑ i, α i * dis x y i ≤ ∑ i : Fin N, (1 : ℝ) := Finset.sum_le_sum (fun i _ => by
        calc α i * dis x y i ≤ α i * 1 := mul_le_mul_of_nonneg_left (dis_le_one _ _ _) (hα.1 i)
          _ ≤ 1 := by linarith [h1 i])
    _ = N := by simp

lemma dc_bddAbove {N : ℕ} (A : Finset (Fin N → Bool)) (x : Fin N → Bool) :
    BddAbove (Set.range fun α : Adm N => hamW A α.1 x) := by
  refine ⟨N, ?_⟩
  rintro _ ⟨α, rfl⟩
  exact hamW_le_card A α.2 x

lemma hamW_le_dc {N : ℕ} (A : Finset (Fin N → Bool)) {α : Fin N → ℝ} (hα : α ∈ Adm N)
    (x : Fin N → Bool) : hamW A α x ≤ dc A x :=
  le_ciSup (dc_bddAbove A x) ⟨α, hα⟩

lemma dc_nonneg {N : ℕ} (A : Finset (Fin N → Bool)) (hA : A.Nonempty) (x : Fin N → Bool) :
    0 ≤ dc A x := by
  have := hamW_le_dc A (zero_mem_Adm N) x
  rwa [hamW_zero A hA] at this

lemma dc_le {N : ℕ} (A : Finset (Fin N → Bool)) (x : Fin N → Bool) {s : ℝ}
    (h : ∀ α ∈ Adm N, hamW A α x ≤ s) : dc A x ≤ s :=
  ciSup_le (fun α => h α.1 α.2)

lemma hamW_smul {N : ℕ} (A : Finset (Fin N → Bool)) (α : Fin N → ℝ) (x : Fin N → Bool)
    {c : ℝ} (hc : 0 ≤ c) : hamW A (c • α) x = c * hamW A α x := by
  unfold hamW
  rw [Real.mul_iInf_of_nonneg hc]
  congr 1; ext y
  rw [Finset.mul_sum]
  congr 1; ext i; simp [mul_assoc]

/-- homogeneity bound: `hamW A β x ≤ ‖β‖₂ · dc A x` for nonnegative `β`. -/
lemma hamW_le_norm_mul_dc {N : ℕ} (A : Finset (Fin N → Bool)) (hA : A.Nonempty)
    {β : Fin N → ℝ} (hβ : ∀ i, 0 ≤ β i) (x : Fin N → Bool) :
    hamW A β x ≤ Real.sqrt (∑ i, β i ^ 2) * dc A x := by
  have hS0 : 0 ≤ ∑ i, β i ^ 2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  rcases eq_or_lt_of_le hS0 with h0 | hpos
  · -- β = 0
    have hβ0 : β = 0 := by
      ext i
      have := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg (β i))).mp h0.symm i (Finset.mem_univ i)
      exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this
    rw [hβ0, hamW_zero A hA]
    exact mul_nonneg (Real.sqrt_nonneg _) (dc_nonneg A hA x)
  · have hn : 0 < Real.sqrt (∑ i, β i ^ 2) := Real.sqrt_pos.mpr hpos
    have hmem : (Real.sqrt (∑ i, β i ^ 2))⁻¹ • β ∈ Adm N := by
      refine ⟨fun i => by simp only [Pi.smul_apply, smul_eq_mul]; exact mul_nonneg (inv_nonneg.mpr hn.le) (hβ i), ?_⟩
      simp only [Pi.smul_apply, smul_eq_mul, mul_pow, ← Finset.mul_sum]
      rw [inv_pow, Real.sq_sqrt hS0, inv_mul_cancel₀ hpos.ne']
    have := hamW_le_dc A hmem x
    have e : β = Real.sqrt (∑ i, β i ^ 2) • ((Real.sqrt (∑ i, β i ^ 2))⁻¹ • β) := by
      rw [smul_smul, mul_inv_cancel₀ hn.ne', one_smul]
    calc hamW A β x = hamW A (Real.sqrt (∑ i, β i ^ 2) • ((Real.sqrt (∑ i, β i ^ 2))⁻¹ • β)) x := by rw [← e]
      _ = Real.sqrt (∑ i, β i ^ 2) * hamW A ((Real.sqrt (∑ i, β i ^ 2))⁻¹ • β) x := hamW_smul A _ x hn.le
      _ ≤ Real.sqrt (∑ i, β i ^ 2) * dc A x := mul_le_mul_of_nonneg_left this hn.le


/-! ### The induction on the dimension -/

/-- section of `A` at last coordinate `ω` -/
def sec {N : ℕ} (A : Finset (Fin (N+1) → Bool)) (ω : Bool) : Finset (Fin N → Bool) :=
  Finset.univ.filter (fun z => (Fin.snoc z ω : Fin (N+1) → Bool) ∈ A)

/-- projection of `A` onto the first `N` coordinates -/
def proj {N : ℕ} (A : Finset (Fin (N+1) → Bool)) : Finset (Fin N → Bool) :=
  Finset.univ.filter (fun z => ∃ ω, (Fin.snoc z ω : Fin (N+1) → Bool) ∈ A)

lemma mem_sec {N : ℕ} (A : Finset (Fin (N+1) → Bool)) (ω : Bool) (z : Fin N → Bool) :
    z ∈ sec A ω ↔ (Fin.snoc z ω : Fin (N+1) → Bool) ∈ A := by
  simp [sec]

lemma mem_proj {N : ℕ} (A : Finset (Fin (N+1) → Bool)) (z : Fin N → Bool) :
    z ∈ proj A ↔ ∃ ω, (Fin.snoc z ω : Fin (N+1) → Bool) ∈ A := by
  simp [proj]

lemma sec_subset_proj {N : ℕ} (A : Finset (Fin (N+1) → Bool)) (ω : Bool) : sec A ω ⊆ proj A := by
  intro z hz; rw [mem_sec] at hz; rw [mem_proj]; exact ⟨ω, hz⟩

lemma card_sec_le {N : ℕ} (A : Finset (Fin (N+1) → Bool)) (ω : Bool) :
    (sec A ω).card ≤ (proj A).card :=
  Finset.card_le_card (sec_subset_proj A ω)

/-- the equivalence `(Fin N → Bool) × Bool ≃ (Fin (N+1) → Bool)` by `snoc` -/
def snocEquivB (N : ℕ) : (Fin N → Bool) × Bool ≃ (Fin (N+1) → Bool) where
  toFun p := Fin.snoc p.1 p.2
  invFun x := (Fin.init x, x (Fin.last N))
  left_inv p := by
    ext j
    · simp [Fin.init_snoc]
    · simp [Fin.snoc_last]
  right_inv x := by
    simp [Fin.snoc_init_self]

lemma sum_univ_snoc {N : ℕ} {M : Type*} [AddCommMonoid M] (f : (Fin (N+1) → Bool) → M) :
    ∑ x, f x = ∑ ω : Bool, ∑ z : Fin N → Bool, f (Fin.snoc z ω) := by
  rw [← (snocEquivB N).sum_comp, Fintype.sum_prod_type, Finset.sum_comm]
  rfl

lemma card_sec_add {N : ℕ} (A : Finset (Fin (N+1) → Bool)) :
    (sec A true).card + (sec A false).card = A.card := by
  have h1 : A.card = ∑ x : Fin (N+1) → Bool, (if x ∈ A then 1 else 0) := by
    rw [Finset.sum_boole]; simp
  rw [h1, sum_univ_snoc, Fintype.sum_bool]
  simp only [sec, Finset.card_filter]

lemma proj_nonempty {N : ℕ} (A : Finset (Fin (N+1) → Bool)) (hA : A.Nonempty) : (proj A).Nonempty := by
  obtain ⟨x, hx⟩ := hA
  refine ⟨Fin.init x, ?_⟩
  rw [mem_proj]
  exact ⟨x (Fin.last N), by rw [Fin.snoc_init_self]; exact hx⟩

lemma sum_dis_snoc {N : ℕ} (α : Fin (N+1) → ℝ) (z y' : Fin N → Bool) (ω ω' : Bool) :
    ∑ i, α i * dis (Fin.snoc z ω) (Fin.snoc y' ω') i
      = ∑ j, α (Fin.castSucc j) * dis z y' j + α (Fin.last N) * (if ω = ω' then 0 else 1) := by
  rw [Fin.sum_univ_castSucc]
  congr 1
  · apply Finset.sum_congr rfl; intro j _
    simp [dis, Fin.snoc_castSucc]
  · simp [dis, Fin.snoc_last]

lemma adm_split {N : ℕ} {α : Fin (N+1) → ℝ} (hα : α ∈ Adm (N+1)) :
    (∀ j, 0 ≤ α (Fin.castSucc j)) ∧ 0 ≤ α (Fin.last N) ∧
      ∑ j, α (Fin.castSucc j) ^ 2 + α (Fin.last N) ^ 2 ≤ 1 := by
  refine ⟨fun j => hα.1 _, hα.1 _, ?_⟩
  have := hα.2
  rwa [Fin.sum_univ_castSucc] at this

lemma hamW_snoc_le_sec {N : ℕ} (A : Finset (Fin (N+1) → Bool)) (α : Fin (N+1) → ℝ)
    (z : Fin N → Bool) (ω : Bool) (hsec : (sec A ω).Nonempty) :
    hamW A α (Fin.snoc z ω) ≤ hamW (sec A ω) (fun j => α (Fin.castSucc j)) z := by
  apply le_hamW _ hsec
  intro y' hy'
  rw [mem_sec] at hy'
  have := hamW_le A α (Fin.snoc z ω) hy'
  rw [sum_dis_snoc] at this
  simpa using this

lemma hamW_snoc_le_proj {N : ℕ} (A : Finset (Fin (N+1) → Bool)) {α : Fin (N+1) → ℝ}
    (hα : α ∈ Adm (N+1)) (z : Fin N → Bool) (ω : Bool) (hA : A.Nonempty) :
    hamW A α (Fin.snoc z ω) ≤ hamW (proj A) (fun j => α (Fin.castSucc j)) z + α (Fin.last N) := by
  rw [← sub_le_iff_le_add]
  apply le_hamW _ (proj_nonempty A hA)
  intro y' hy'
  rw [mem_proj] at hy'
  obtain ⟨ω', hω'⟩ := hy'
  have := hamW_le A α (Fin.snoc z ω) hω'
  rw [sum_dis_snoc] at this
  have hl : α (Fin.last N) * (if ω = ω' then 0 else 1) ≤ α (Fin.last N) := by
    split_ifs
    · simp [hα.1 _]
    · simp
  linarith

lemma sq_le_of_le_sqrt {h R : ℝ} (hh : 0 ≤ h) (hR : 0 ≤ R) (hle : h ≤ Real.sqrt R) : h ^ 2 ≤ R := by
  calc h ^ 2 ≤ Real.sqrt R ^ 2 := pow_le_pow_left₀ hh hle 2
    _ = R := Real.sq_sqrt hR

/-- Pointwise key inequality in the induction (nonempty section case). -/
lemma dc_snoc_sq_le {N : ℕ} (A : Finset (Fin (N+1) → Bool)) (hA : A.Nonempty)
    (z : Fin N → Bool) (ω : Bool) {l : ℝ} (h0 : 0 ≤ l) (h1 : l ≤ 1)
    (hsec : (sec A ω).Nonempty) :
    dc A (Fin.snoc z ω) ^ 2 ≤ l * dc (sec A ω) z ^ 2 + (1 - l) * dc (proj A) z ^ 2 + (1 - l) ^ 2 := by
  have hd1 := dc_nonneg _ hsec z
  have hd2 := dc_nonneg _ (proj_nonempty A hA) z
  have hR : 0 ≤ l * dc (sec A ω) z ^ 2 + (1 - l) * dc (proj A) z ^ 2 + (1 - l) ^ 2 := by
    have : 0 ≤ 1 - l := by linarith
    positivity
  apply sq_le_of_le_sqrt (dc_nonneg A hA _) hR
  apply dc_le
  intro α hα
  obtain ⟨hβ, ha, hnorm⟩ := adm_split hα
  have hpos := hamW_nonneg A hA hα.1 (Fin.snoc z ω)
  have hI1 := hamW_snoc_le_sec A α z ω hsec
  have hI2 := hamW_snoc_le_proj A hα z ω hA
  have hh1 := hamW_le_norm_mul_dc (sec A ω) hsec hβ z
  have hh2 := hamW_le_norm_mul_dc (proj A) (proj_nonempty A hA) hβ z
  set h := hamW A α (Fin.snoc z ω)
  set nb := Real.sqrt (∑ j, α (Fin.castSucc j) ^ 2) with hnb
  set a := α (Fin.last N)
  set d1 := dc (sec A ω) z
  set d2 := dc (proj A) z
  have hnb0 : 0 ≤ nb := Real.sqrt_nonneg _
  have hnbsq : nb ^ 2 = ∑ j, α (Fin.castSucc j) ^ 2 :=
    Real.sq_sqrt (Finset.sum_nonneg (fun j _ => sq_nonneg _))
  have hnorm' : nb ^ 2 + a ^ 2 ≤ 1 := by rw [hnbsq]; exact hnorm
  rw [Real.le_sqrt hpos hR]
  set P := l * d1 + (1 - l) * d2
  set Q := 1 - l
  have hQ : 0 ≤ Q := by simp only [Q]; linarith
  have hP : 0 ≤ P := by simp only [P]; positivity
  have hh : h ≤ nb * P + a * Q := by
    have e1 : l * h ≤ l * (nb * d1) := mul_le_mul_of_nonneg_left (hI1.trans hh1) h0
    have e2 : (1 - l) * h ≤ (1 - l) * (nb * d2 + a) := mul_le_mul_of_nonneg_left (hI2.trans (by linarith)) hQ
    simp only [P, Q]; nlinarith
  have hcs : (nb * P + a * Q) ^ 2 ≤ (nb ^ 2 + a ^ 2) * (P ^ 2 + Q ^ 2) := by
    nlinarith [sq_nonneg (nb * Q - a * P)]
  have hcs2 : (nb ^ 2 + a ^ 2) * (P ^ 2 + Q ^ 2) ≤ P ^ 2 + Q ^ 2 := by
    have := mul_le_mul_of_nonneg_right hnorm' (by positivity : 0 ≤ P ^ 2 + Q ^ 2)
    linarith
  have hPsq : P ^ 2 ≤ l * d1 ^ 2 + (1 - l) * d2 ^ 2 := by
    simp only [P]
    nlinarith [mul_nonneg (mul_nonneg h0 hQ) (sq_nonneg (d1 - d2))]
  have hsq : h ^ 2 ≤ (nb * P + a * Q) ^ 2 := pow_le_pow_left₀ hpos hh 2
  simp only [Q] at hcs hcs2
  linarith

/-- Pointwise key inequality in the induction (empty section case). -/
lemma dc_snoc_sq_le' {N : ℕ} (A : Finset (Fin (N+1) → Bool)) (hA : A.Nonempty)
    (z : Fin N → Bool) (ω : Bool) :
    dc A (Fin.snoc z ω) ^ 2 ≤ dc (proj A) z ^ 2 + 1 := by
  have hd2 := dc_nonneg _ (proj_nonempty A hA) z
  have hR : 0 ≤ dc (proj A) z ^ 2 + 1 := by positivity
  apply sq_le_of_le_sqrt (dc_nonneg A hA _) hR
  apply dc_le
  intro α hα
  obtain ⟨hβ, ha, hnorm⟩ := adm_split hα
  have hpos := hamW_nonneg A hA hα.1 (Fin.snoc z ω)
  have hI2 := hamW_snoc_le_proj A hα z ω hA
  have hh2 := hamW_le_norm_mul_dc (proj A) (proj_nonempty A hA) hβ z
  set h := hamW A α (Fin.snoc z ω)
  set nb := Real.sqrt (∑ j, α (Fin.castSucc j) ^ 2) with hnb
  set a := α (Fin.last N)
  set d2 := dc (proj A) z
  have hnb0 : 0 ≤ nb := Real.sqrt_nonneg _
  have hnbsq : nb ^ 2 = ∑ j, α (Fin.castSucc j) ^ 2 :=
    Real.sq_sqrt (Finset.sum_nonneg (fun j _ => sq_nonneg _))
  have hnorm' : nb ^ 2 + a ^ 2 ≤ 1 := by rw [hnbsq]; exact hnorm
  rw [Real.le_sqrt hpos hR]
  have hh : h ≤ nb * d2 + a := hI2.trans (by linarith)
  have hcs : (nb * d2 + a) ^ 2 ≤ (nb ^ 2 + a ^ 2) * (d2 ^ 2 + 1) := by
    nlinarith [sq_nonneg (nb - a * d2)]
  have hcs2 : (nb ^ 2 + a ^ 2) * (d2 ^ 2 + 1) ≤ d2 ^ 2 + 1 := by
    have := mul_le_mul_of_nonneg_right hnorm' (by positivity : 0 ≤ d2 ^ 2 + 1)
    linarith
  have hsq : h ^ 2 ≤ (nb * d2 + a) ^ 2 := pow_le_pow_left₀ hpos hh 2
  linarith

/-- Talagrand's convex distance inequality on the discrete cube (sum form). -/
theorem dc_exp_sum : ∀ (N : ℕ) (A : Finset (Fin N → Bool)), A.Nonempty →
    ∑ x, Real.exp (dc A x ^ 2 / 4) ≤ (4:ℝ) ^ N / A.card := by
  intro N
  induction N with
  | zero =>
    intro A hA
    have hdc : ∀ x, dc A x = 0 := by
      intro x
      apply le_antisymm _ (dc_nonneg A hA x)
      apply dc_le
      intro α _
      obtain ⟨y, hy⟩ := hA
      have := hamW_le A α x hy
      simpa using this
    have hcard : A.card = 1 := by
      have h1 : A.card ≤ 1 := by
        have := Finset.card_le_univ A
        simpa using this
      have h2 : 0 < A.card := hA.card_pos
      omega
    simp [hdc, hcard]
  | succ N ih =>
    intro A hA
    have hB := proj_nonempty A hA
    have hcB : (0:ℝ) < (proj A).card := by exact_mod_cast hB.card_pos
    set G' : ℝ := (4:ℝ) ^ N / (proj A).card with hG'
    have hG'pos : 0 < G' := by positivity
    have hG : ∑ z, Real.exp (dc (proj A) z ^ 2 / 4) ≤ G' := ih _ hB
    -- per-slice bound
    have hslice : ∀ ω : Bool, ∑ z, Real.exp (dc A (Fin.snoc z ω) ^ 2 / 4)
        ≤ G' * (2 - (sec A ω).card / (proj A).card) := by
      intro ω
      rcases (sec A ω).eq_empty_or_nonempty with hs | hs
      · rw [hs]; simp only [Finset.card_empty, Nat.cast_zero, zero_div, sub_zero]
        calc ∑ z, Real.exp (dc A (Fin.snoc z ω) ^ 2 / 4)
            ≤ ∑ z, Real.exp (1/4) * Real.exp (dc (proj A) z ^ 2 / 4) := by
              apply Finset.sum_le_sum; intro z _
              rw [← Real.exp_add]
              apply Real.exp_le_exp.mpr
              have := dc_snoc_sq_le' A hA z ω
              linarith
          _ = Real.exp (1/4) * ∑ z, Real.exp (dc (proj A) z ^ 2 / 4) := by rw [Finset.mul_sum]
          _ ≤ 2 * G' := by
              have := exp_quarter_lt
              have hS : 0 ≤ ∑ z, Real.exp (dc (proj A) z ^ 2 / 4) :=
                Finset.sum_nonneg (fun z _ => (Real.exp_pos _).le)
              nlinarith
          _ = G' * 2 := by ring
      · have hcS : (0:ℝ) < (sec A ω).card := by exact_mod_cast hs.card_pos
        set g : ℝ := (sec A ω).card / (proj A).card with hg
        have hg0 : 0 < g := by positivity
        have hg1 : g ≤ 1 := by
          rw [hg, div_le_one hcB]; exact_mod_cast card_sec_le A ω
        obtain ⟨l, h0, h1, hkey⟩ := talagrand_key hg0 hg1
        have hF : ∑ z, Real.exp (dc (sec A ω) z ^ 2 / 4) ≤ (4:ℝ) ^ N / (sec A ω).card := ih _ hs
        have hF' : (4:ℝ) ^ N / (sec A ω).card = G' / g := by
          rw [hG', hg]; field_simp
        calc ∑ z, Real.exp (dc A (Fin.snoc z ω) ^ 2 / 4)
            ≤ ∑ z, Real.exp ((1 - l) ^ 2 / 4) *
                (Real.exp (dc (sec A ω) z ^ 2 / 4) ^ l * Real.exp (dc (proj A) z ^ 2 / 4) ^ (1 - l)) := by
              apply Finset.sum_le_sum; intro z _
              rw [← Real.exp_mul, ← Real.exp_mul, ← Real.exp_add, ← Real.exp_add]
              apply Real.exp_le_exp.mpr
              have := dc_snoc_sq_le A hA z ω h0 h1 hs
              linarith
          _ = Real.exp ((1 - l) ^ 2 / 4) *
                ∑ z, Real.exp (dc (sec A ω) z ^ 2 / 4) ^ l * Real.exp (dc (proj A) z ^ 2 / 4) ^ (1 - l) := by
              rw [Finset.mul_sum]
          _ ≤ Real.exp ((1 - l) ^ 2 / 4) *
                ((∑ z, Real.exp (dc (sec A ω) z ^ 2 / 4)) ^ l * (∑ z, Real.exp (dc (proj A) z ^ 2 / 4)) ^ (1 - l)) := by
              apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
              exact holder_sum _ _ (fun z => Real.exp_pos _) (fun z => Real.exp_pos _) l h0 h1
          _ ≤ Real.exp ((1 - l) ^ 2 / 4) * ((G' / g) ^ l * G' ^ (1 - l)) := by
              apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
              apply mul_le_mul
              · rw [← hF']
                exact Real.rpow_le_rpow (Finset.sum_nonneg (fun z _ => (Real.exp_pos _).le)) hF h0
              · exact Real.rpow_le_rpow (Finset.sum_nonneg (fun z _ => (Real.exp_pos _).le)) hG (by linarith)
              · positivity
              · positivity
          _ = Real.exp ((1 - l) ^ 2 / 4) * (G' / g ^ l) := by
              rw [Real.div_rpow hG'pos.le hg0.le, div_mul_eq_mul_div, ← Real.rpow_add hG'pos]
              simp
          _ ≤ ((2 - g) * g ^ l) * (G' / g ^ l) := by
              apply mul_le_mul_of_nonneg_right hkey (by positivity)
          _ = G' * (2 - g) := by
              have : 0 < g ^ l := Real.rpow_pos_of_pos hg0 l
              field_simp
    -- sum over the two slices
    rw [sum_univ_snoc, Fintype.sum_bool]
    have ht := hslice true
    have hf := hslice false
    have hcard : ((sec A true).card : ℝ) + (sec A false).card = A.card := by
      exact_mod_cast card_sec_add A
    have hA2 : (A.card : ℝ) ≤ 2 * (proj A).card := by
      rw [← hcard]
      have := card_sec_le A true
      have := card_sec_le A false
      push_cast
      have h1 : ((sec A true).card : ℝ) ≤ (proj A).card := by exact_mod_cast card_sec_le A true
      have h2 : ((sec A false).card : ℝ) ≤ (proj A).card := by exact_mod_cast card_sec_le A false
      linarith
    have hApos : (0:ℝ) < A.card := by exact_mod_cast hA.card_pos
    have hsum : G' * (2 - (sec A true).card / (proj A).card) + G' * (2 - (sec A false).card / (proj A).card)
        = G' * (4 - A.card / (proj A).card) := by
      rw [← hcard]; field_simp; ring
    have hfinal : G' * (4 - A.card / (proj A).card) ≤ (4:ℝ) ^ (N+1) / A.card := by
      rw [hG', pow_succ]
      have h4 : (0:ℝ) < 4 ^ N := by positivity
      have e1 : (4:ℝ) ^ N / (proj A).card * (4 - A.card / (proj A).card)
          = 4 ^ N * (4 * (proj A).card - A.card) / ((proj A).card * (proj A).card) := by
        field_simp
      rw [e1, div_le_div_iff₀ (by positivity) hApos]
      nlinarith [sq_nonneg (2 * ((proj A).card : ℝ) - A.card), mul_pos h4 hcB]
    linarith


/-! ### Markov and the uniform measure on the cube -/

lemma card_dc_ge_mul_exp_le {N : ℕ} (A : Finset (Fin N → Bool)) (hA : A.Nonempty) {r : ℝ} (hr : 0 ≤ r) :
    ((Finset.univ.filter (fun x => r ≤ dc A x)).card : ℝ) * Real.exp (r ^ 2 / 4) ≤ (4:ℝ) ^ N / A.card := by
  calc ((Finset.univ.filter (fun x => r ≤ dc A x)).card : ℝ) * Real.exp (r ^ 2 / 4)
      = ∑ x ∈ Finset.univ.filter (fun x => r ≤ dc A x), Real.exp (r ^ 2 / 4) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ x ∈ Finset.univ.filter (fun x => r ≤ dc A x), Real.exp (dc A x ^ 2 / 4) := by
        apply Finset.sum_le_sum
        intro x hx
        rw [Finset.mem_filter] at hx
        apply Real.exp_le_exp.mpr
        have := pow_le_pow_left₀ hr hx.2 2
        linarith
    _ ≤ ∑ x, Real.exp (dc A x ^ 2 / 4) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun x _ _ => (Real.exp_pos _).le)
    _ ≤ (4:ℝ) ^ N / A.card := dc_exp_sum N A hA

lemma spMeasure_singleton {N : ℕ} (b : Fin N → Bool) :
    Komlos.spMeasure N {b} = (2⁻¹ : ℝ≥0∞) ^ N := by
  unfold Komlos.spMeasure
  have : ({b} : Set (Fin N → Bool)) = Set.pi Set.univ (fun i => {b i}) := by
    ext y; simp [funext_iff]
  rw [this, MeasureTheory.Measure.pi_pi]
  simp only [PMF.toMeasure_apply_singleton _ _ (MeasurableSet.singleton _), PMF.uniformOfFintype_apply,
    Fintype.card_bool, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  norm_num

lemma spMeasure_apply {N : ℕ} (S : Set (Fin N → Bool)) :
    Komlos.spMeasure N S = ((Finset.univ.filter (fun x => x ∈ S)).card : ℝ≥0∞) / 2 ^ N := by
  have hS : S = ↑(Finset.univ.filter (fun x => x ∈ S)) := by ext x; simp
  conv_lhs => rw [hS]
  rw [← MeasureTheory.sum_measure_singleton]
  simp only [spMeasure_singleton, Finset.sum_const, nsmul_eq_mul]
  rw [div_eq_mul_inv, ENNReal.inv_pow]

lemma spMeasure_le_ofReal {N : ℕ} (S : Set (Fin N → Bool)) {c : ℝ}
    (h : ((Finset.univ.filter (fun x => x ∈ S)).card : ℝ) / 2 ^ N ≤ c) :
    Komlos.spMeasure N S ≤ ENNReal.ofReal c := by
  rw [spMeasure_apply]
  have e : ((Finset.univ.filter (fun x => x ∈ S)).card : ℝ≥0∞) / 2 ^ N
      = ENNReal.ofReal (((Finset.univ.filter (fun x => x ∈ S)).card : ℝ) / 2 ^ N) := by
    rw [ENNReal.ofReal_div_of_pos (by positivity), ENNReal.ofReal_natCast, ENNReal.ofReal_pow (by norm_num)]
    norm_num
  rw [e]
  exact ENNReal.ofReal_le_ofReal h

/-- Probability form of the convex distance inequality: for `A` with `2^N ≤ 2 |A|`,
`P(dc A ε ≥ r) ≤ 2 exp(-r²/4)`. -/
lemma spMeasure_dc_ge_le {N : ℕ} (A : Finset (Fin N → Bool)) (hA : A.Nonempty)
    (hA2 : (2:ℝ) ^ N ≤ 2 * A.card) {r : ℝ} (hr : 0 ≤ r) :
    Komlos.spMeasure N {ε | r ≤ dc A ε} ≤ ENNReal.ofReal (2 * Real.exp (-(r ^ 2 / 4))) := by
  apply spMeasure_le_ofReal
  have h := card_dc_ge_mul_exp_le A hA hr
  have hc : (0:ℝ) < A.card := by exact_mod_cast hA.card_pos
  have hex : 0 < Real.exp (r ^ 2 / 4) := Real.exp_pos _
  have h4 : (4:ℝ) ^ N = 2 ^ N * 2 ^ N := by rw [← mul_pow]; norm_num
  rw [Real.exp_neg]
  have hS : (Finset.univ.filter (fun x => x ∈ {ε : Fin N → Bool | r ≤ dc A ε})) = Finset.univ.filter (fun x => r ≤ dc A x) := by
    congr 1
  rw [hS]
  set C : ℝ := ((Finset.univ.filter (fun x => r ≤ dc A x)).card : ℝ)
  rw [div_le_iff₀ (by positivity)]
  -- C * e ≤ 4^N / |A|  and 2^N ≤ 2|A|  ⇒ C ≤ 2 e⁻¹ 2^N
  rw [h4, le_div_iff₀ hc] at h
  have h2N : (0:ℝ) < 2 ^ N := by positivity
  have hC : (0:ℝ) ≤ C := by positivity
  have e1 : 2 * (Real.exp (r ^ 2 / 4))⁻¹ * 2 ^ N = 2 * 2 ^ N / Real.exp (r ^ 2 / 4) := by ring
  rw [e1, le_div_iff₀ hex]
  nlinarith [mul_le_mul_of_nonneg_left hA2 (mul_nonneg h2N.le (mul_nonneg hC hex.le))]


/-! ### The rearrangement sums -/

section Banach
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] {N : ℕ}

lemma normRearr_nonneg (x : Fin N → W) (i : ℕ) : 0 ≤ normRearr x i := by
  unfold normRearr
  split_ifs with h
  · apply le_csSup
    · refine ⟨∑ j, ‖x j‖, ?_⟩
      rintro t ht
      simp only [Set.mem_setOf_eq] at ht
      have hpos : 0 < (Finset.univ.filter (fun j => t ≤ ‖x j‖)).card := by omega
      obtain ⟨j, hj⟩ := Finset.card_pos.mp hpos
      rw [Finset.mem_filter] at hj
      calc t ≤ ‖x j‖ := hj.2
        _ ≤ ∑ j, ‖x j‖ := Finset.single_le_sum (fun j _ => norm_nonneg (x j)) (Finset.mem_univ j)
    · simp only [Set.mem_setOf_eq]
      have : (Finset.univ.filter (fun j => (0:ℝ) ≤ ‖x j‖)) = Finset.univ := by
        ext j; simp [norm_nonneg]
      rw [this, Finset.card_univ, Fintype.card_fin]; exact h.2
  · exact le_rfl

lemma le_normRearr (x : Fin N → W) {i : ℕ} (hi1 : 1 ≤ i) (hiN : i ≤ N) {t : ℝ}
    (ht : i ≤ (Finset.univ.filter (fun j => t ≤ ‖x j‖)).card) : t ≤ normRearr x i := by
  unfold normRearr
  rw [if_pos ⟨hi1, hiN⟩]
  apply le_csSup
  · refine ⟨∑ j, ‖x j‖, ?_⟩
    rintro s hs
    simp only [Set.mem_setOf_eq] at hs
    have hpos : 0 < (Finset.univ.filter (fun j => s ≤ ‖x j‖)).card := by omega
    obtain ⟨j, hj⟩ := Finset.card_pos.mp hpos
    rw [Finset.mem_filter] at hj
    calc s ≤ ‖x j‖ := hj.2
      _ ≤ ∑ j, ‖x j‖ := Finset.single_le_sum (fun j _ => norm_nonneg (x j)) (Finset.mem_univ j)
  · exact ht

lemma topSum_succ (x : Fin N → W) (n : ℕ) : topSum x (n + 1) = topSum x n + normRearr x (n + 1) := by
  unfold topSum
  rw [Finset.sum_Icc_succ_top (by omega)]

lemma topSum_mono (x : Fin N → W) {m n : ℕ} (h : m ≤ n) : topSum x m ≤ topSum x n := by
  unfold topSum
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro i hi; simp only [Finset.mem_Icc] at hi ⊢; omega
  · intro i _ _; exact normRearr_nonneg x i

lemma sum_norm_le_topSum (x : Fin N → W) : ∀ (n : ℕ) (J : Finset (Fin N)), J.card = n →
    ∑ i ∈ J, ‖x i‖ ≤ topSum x n := by
  intro n
  induction n with
  | zero =>
    intro J hJ
    rw [Finset.card_eq_zero] at hJ
    subst hJ; simp [topSum]
  | succ n ih =>
    intro J hJ
    have hJne : J.Nonempty := by rw [← Finset.card_pos]; omega
    obtain ⟨i0, hi0, hmin⟩ := Finset.exists_min_image J (fun i => ‖x i‖) hJne
    have hcard : (J.erase i0).card = n := by rw [Finset.card_erase_of_mem hi0]; omega
    have h1 := ih (J.erase i0) hcard
    have h2 : ‖x i0‖ ≤ normRearr x (n + 1) := by
      apply le_normRearr x (by omega)
      · have := Finset.card_le_univ J; simp at this; omega
      · rw [← hJ]
        apply Finset.card_le_card
        intro j hj
        rw [Finset.mem_filter]
        exact ⟨Finset.mem_univ _, hmin j hj⟩
    rw [← Finset.add_sum_erase J _ hi0, topSum_succ]
    linarith

/-! ### Signed sums -/

lemma norm_sgn_smul (b : Bool) (w : W) : ‖sgn b • w‖ = ‖w‖ := by
  unfold sgn; split_ifs <;> simp

/-- the vector `x` with the coordinates in `J` set to zero -/
def zeroOn (x : Fin N → W) (J : Finset (Fin N)) : Fin N → W := fun i => if i ∈ J then 0 else x i

lemma signedSum_zeroOn (ε : Fin N → Bool) (x : Fin N → W) (J : Finset (Fin N)) :
    signedSum ε x = signedSum ε (zeroOn x J) + ∑ i ∈ J, sgn (ε i) • x i := by
  unfold signedSum
  have h1 : ∑ i ∈ J, sgn (ε i) • zeroOn x J i = 0 := by
    apply Finset.sum_eq_zero; intro i hi; simp [zeroOn, hi]
  have h2 : ∑ i ∈ Jᶜ, sgn (ε i) • zeroOn x J i = ∑ i ∈ Jᶜ, sgn (ε i) • x i := by
    apply Finset.sum_congr rfl; intro i hi; rw [Finset.mem_compl] at hi; simp [zeroOn, hi]
  rw [← Finset.sum_add_sum_compl J (fun i => sgn (ε i) • x i),
    ← Finset.sum_add_sum_compl J (fun i => sgn (ε i) • zeroOn x J i), h1, h2]
  abel

lemma norm_signedSum_le_zeroOn (ε : Fin N → Bool) (x : Fin N → W) (J : Finset (Fin N)) :
    ‖signedSum ε x‖ ≤ ‖signedSum ε (zeroOn x J)‖ + ∑ i ∈ J, ‖x i‖ := by
  rw [signedSum_zeroOn ε x J]
  refine (norm_add_le _ _).trans ?_
  gcongr
  refine (norm_sum_le _ _).trans ?_
  apply le_of_eq
  apply Finset.sum_congr rfl; intro i _; exact norm_sgn_smul _ _

/-- flip the signs in `J` -/
def flipOn (J : Finset (Fin N)) (ε : Fin N → Bool) : Fin N → Bool := fun i => if i ∈ J then !ε i else ε i

lemma flipOn_involutive (J : Finset (Fin N)) : Function.Involutive (flipOn J) := by
  intro ε; ext i; simp [flipOn]; split_ifs <;> simp

lemma sgn_not (b : Bool) : sgn (!b) = - sgn b := by
  cases b <;> simp [sgn]

lemma two_smul_signedSum_zeroOn (ε : Fin N → Bool) (x : Fin N → W) (J : Finset (Fin N)) :
    (2:ℝ) • signedSum ε (zeroOn x J) = signedSum ε x + signedSum (flipOn J ε) x := by
  unfold signedSum zeroOn flipOn
  rw [Finset.smul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  split_ifs with h
  · simp [sgn_not]
  · rw [smul_smul, ← add_smul]; congr 1; ring

lemma Eeps_zeroOn_le (x : Fin N → W) (J : Finset (Fin N)) : Eeps (zeroOn x J) ≤ Eeps x := by
  unfold Eeps
  have hflip : ∑ ε : Fin N → Bool, ((2:ℝ) ^ N)⁻¹ * ‖signedSum (flipOn J ε) x‖
      = ∑ ε : Fin N → Bool, ((2:ℝ) ^ N)⁻¹ * ‖signedSum ε x‖ :=
    Equiv.sum_comp (Function.Involutive.toPerm (flipOn J) (flipOn_involutive J)) (fun ε => ((2:ℝ) ^ N)⁻¹ * ‖signedSum ε x‖)
  have hpt : ∀ ε : Fin N → Bool, ((2:ℝ) ^ N)⁻¹ * ‖signedSum ε (zeroOn x J)‖
      ≤ (((2:ℝ) ^ N)⁻¹ * ‖signedSum ε x‖ + ((2:ℝ) ^ N)⁻¹ * ‖signedSum (flipOn J ε) x‖) / 2 := by
    intro ε
    have h := norm_add_le (signedSum ε x) (signedSum (flipOn J ε) x)
    rw [← two_smul_signedSum_zeroOn, norm_smul, Real.norm_ofNat] at h
    have hp : (0:ℝ) ≤ ((2:ℝ) ^ N)⁻¹ := by positivity
    rw [← mul_add, mul_div_assoc]
    apply mul_le_mul_of_nonneg_left _ hp
    linarith
  calc ∑ ε : Fin N → Bool, ((2:ℝ) ^ N)⁻¹ * ‖signedSum ε (zeroOn x J)‖
      ≤ ∑ ε : Fin N → Bool, (((2:ℝ) ^ N)⁻¹ * ‖signedSum ε x‖ + ((2:ℝ) ^ N)⁻¹ * ‖signedSum (flipOn J ε) x‖) / 2 :=
        Finset.sum_le_sum (fun ε _ => hpt ε)
    _ = (∑ ε : Fin N → Bool, ((2:ℝ) ^ N)⁻¹ * ‖signedSum ε x‖ + ∑ ε : Fin N → Bool, ((2:ℝ) ^ N)⁻¹ * ‖signedSum (flipOn J ε) x‖) / 2 := by
        rw [← Finset.sum_div, Finset.sum_add_distrib]
    _ = ∑ ε : Fin N → Bool, ((2:ℝ) ^ N)⁻¹ * ‖signedSum ε x‖ := by rw [hflip]; ring

lemma Eeps_nonneg (x : Fin N → W) : 0 ≤ Eeps x :=
  Finset.sum_nonneg (fun ε _ => mul_nonneg (by positivity) (norm_nonneg _))

lemma sum_norm_signedSum (x : Fin N → W) :
    ∑ ε : Fin N → Bool, ‖signedSum ε x‖ = 2 ^ N * Eeps x := by
  unfold Eeps
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro ε _
  rw [← mul_assoc, mul_inv_cancel₀ (by positivity), one_mul]

/-! ### The sets `sigmaBall` and `kSigma` -/

lemma sum_sq_le_sigmaSq (y : Fin N → W) {w : W →L[ℝ] ℝ} (hw : ‖w‖ ≤ 1) :
    ∑ i, (w (y i)) ^ 2 ≤ sigmaSq y := by
  unfold sigmaSq
  apply le_ciSup (f := fun w : {w : W →L[ℝ] ℝ // ‖w‖ ≤ 1} => ∑ i, (w.1 (y i)) ^ 2) _ ⟨w, hw⟩
  refine ⟨∑ i, ‖y i‖ ^ 2, ?_⟩
  rintro _ ⟨v, rfl⟩
  apply Finset.sum_le_sum; intro i _
  have h1 : |v.1 (y i)| ≤ ‖y i‖ := by
    calc |v.1 (y i)| = ‖v.1 (y i)‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖v.1‖ * ‖y i‖ := v.1.le_opNorm _
      _ ≤ 1 * ‖y i‖ := by gcongr; exact v.2
      _ = ‖y i‖ := one_mul _
  calc (v.1 (y i)) ^ 2 = |v.1 (y i)| ^ 2 := (sq_abs _).symm
    _ ≤ ‖y i‖ ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h1 2

lemma sigmaSq_zero : sigmaSq (fun _ : Fin N => (0 : W)) = 0 := by
  unfold sigmaSq
  haveI : Nonempty {w : W →L[ℝ] ℝ // ‖w‖ ≤ 1} := ⟨⟨0, by simp⟩⟩
  simp

lemma zero_mem_sigmaBall {b : ℝ} (hb : 0 < b) : (fun _ : Fin N => (0 : W)) ∈ sigmaBall b := by
  unfold sigmaBall
  simp only [Set.mem_setOf_eq, sigmaSq_zero, Real.sqrt_zero]
  exact hb.le

lemma sigmaSq_le_of_mem_sigmaBall {b : ℝ} (hb : 0 < b) {y : Fin N → W} (hy : y ∈ sigmaBall b) :
    sigmaSq y ≤ b ^ 2 := by
  unfold sigmaBall at hy
  simp only [Set.mem_setOf_eq] at hy
  rcases le_or_gt 0 (sigmaSq y) with h | h
  · calc sigmaSq y = Real.sqrt (sigmaSq y) ^ 2 := (Real.sq_sqrt h).symm
      _ ≤ b ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) hy 2
  · nlinarith

/-- the mismatch set of `x` relative to a `q`-tuple `y` -/
noncomputable def mismatch (q : ℕ) (x : Fin N → W) (y : Fin q → Fin N → W) : Finset (Fin N) :=
  Finset.univ.filter (fun i => ∀ l, x i ≠ y l i)

lemma kSigma_attained (q : ℕ) {b : ℝ} (hb : 0 < b) (x : Fin N → W) :
    ∃ y : Fin q → Fin N → W, (∀ l, y l ∈ sigmaBall b) ∧
      kSigma q b x = ((mismatch q x y).card : ℕ∞) := by
  classical
  let S : Set ℕ := {n | ∃ y : Fin q → Fin N → W, (∀ l, y l ∈ sigmaBall b) ∧ (mismatch q x y).card = n}
  have hS : S.Nonempty := by
    refine ⟨(mismatch q x (fun _ _ => (0:W))).card, ?_⟩
    show ∃ y : Fin q → Fin N → W, (∀ l, y l ∈ sigmaBall b) ∧ (mismatch q x y).card = _
    exact ⟨fun _ _ => (0:W), fun _ => zero_mem_sigmaBall hb, rfl⟩
  have hmem : sInf S ∈ S := Nat.sInf_mem hS
  obtain ⟨y, hy, hcard⟩ : ∃ y : Fin q → Fin N → W, (∀ l, y l ∈ sigmaBall b) ∧ (mismatch q x y).card = sInf S := hmem
  refine ⟨y, hy, ?_⟩
  unfold kSigma qPointDist
  apply le_antisymm
  · exact iInf_le_of_le y (iInf_le_of_le hy le_rfl)
  · apply le_iInf; intro y'; apply le_iInf; intro hy'
    rw [hcard]
    have hmem' : (mismatch q x y').card ∈ S := ⟨y', hy', rfl⟩
    exact_mod_cast Nat.sInf_le hmem'

lemma topSumE_kSigma (q : ℕ) {b : ℝ} (hb : 0 < b) (x : Fin N → W) :
    ∃ y : Fin q → Fin N → W, (∀ l, y l ∈ sigmaBall b) ∧
      topSumE x (kSigma q b x) = topSum x (mismatch q x y).card := by
  obtain ⟨y, hy, hk⟩ := kSigma_attained q hb x
  refine ⟨y, hy, ?_⟩
  unfold topSumE
  rw [hk]
  have hle : (mismatch q x y).card ≤ N := by
    have := Finset.card_le_univ (mismatch q x y); simpa using this
  have : min ((mismatch q x y).card : ℕ∞) (N : ℕ∞) = ((mismatch q x y).card : ℕ∞) := by
    rw [min_eq_left]; exact_mod_cast hle
  rw [this, ENat.toNat_natCast]

end Banach


/-! ### Assembly -/

section Main
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] {N : ℕ}

lemma sum_sq_zeroOn_le (q : ℕ) {b : ℝ} (hb : 0 < b) (x : Fin N → W) (y : Fin q → Fin N → W)
    (hy : ∀ l, y l ∈ sigmaBall b) {w : W →L[ℝ] ℝ} (hw : ‖w‖ ≤ 1) :
    ∑ i, (w (zeroOn x (mismatch q x y) i)) ^ 2 ≤ q * b ^ 2 := by
  calc ∑ i, (w (zeroOn x (mismatch q x y) i)) ^ 2 ≤ ∑ i, ∑ l, (w (y l i)) ^ 2 := by
        apply Finset.sum_le_sum; intro i _
        by_cases hi : i ∈ mismatch q x y
        · simp only [zeroOn, if_pos hi, map_zero]
          norm_num
          exact Finset.sum_nonneg (fun l _ => sq_nonneg _)
        · have hi' := hi
          simp only [mismatch, Finset.mem_filter, Finset.mem_univ, true_and, not_forall, not_not] at hi
          obtain ⟨l, hl⟩ := hi
          simp only [zeroOn, if_neg hi', hl]
          exact Finset.single_le_sum (fun l _ => sq_nonneg (w (y l i))) (Finset.mem_univ l)
    _ = ∑ l, ∑ i, (w (y l i)) ^ 2 := Finset.sum_comm
    _ ≤ ∑ l : Fin q, b ^ 2 := Finset.sum_le_sum (fun l _ =>
        (sum_sq_le_sigmaSq (y l) hw).trans (sigmaSq_le_of_mem_sigmaBall hb (hy l)))
    _ = q * b ^ 2 := by simp

lemma abs_sgn_sub_le (a b : Bool) : |sgn a - sgn b| ≤ 2 * (if a = b then (0:ℝ) else 1) := by
  cases a <;> cases b <;> simp [sgn] <;> norm_num

lemma apply_signedSum_le (x' : Fin N → W) (ε ε' : Fin N → Bool) (w : W →L[ℝ] ℝ) (hw : ‖w‖ ≤ 1) :
    w (signedSum ε x') ≤ ‖signedSum ε' x'‖ + 2 * ∑ i, |w (x' i)| * dis ε ε' i := by
  have e : signedSum ε x' = signedSum ε' x' + ∑ i, (sgn (ε i) - sgn (ε' i)) • x' i := by
    unfold signedSum
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro i _
    rw [sub_smul]; abel
  rw [e, map_add, map_sum]
  have h1 : w (signedSum ε' x') ≤ ‖signedSum ε' x'‖ := by
    calc w (signedSum ε' x') ≤ |w (signedSum ε' x')| := le_abs_self _
      _ = ‖w (signedSum ε' x')‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖w‖ * ‖signedSum ε' x'‖ := w.le_opNorm _
      _ ≤ 1 * ‖signedSum ε' x'‖ := by gcongr
      _ = _ := one_mul _
  have h2 : ∑ i, w ((sgn (ε i) - sgn (ε' i)) • x' i) ≤ 2 * ∑ i, |w (x' i)| * dis ε ε' i := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum; intro i _
    rw [map_smul, smul_eq_mul]
    calc (sgn (ε i) - sgn (ε' i)) * w (x' i) ≤ |(sgn (ε i) - sgn (ε' i)) * w (x' i)| := le_abs_self _
      _ = |sgn (ε i) - sgn (ε' i)| * |w (x' i)| := abs_mul _ _
      _ ≤ (2 * dis ε ε' i) * |w (x' i)| := by
          apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
          exact abs_sgn_sub_le _ _
      _ = 2 * (|w (x' i)| * dis ε ε' i) := by ring
  linarith

lemma card_univ_bool_fun : (Finset.univ : Finset (Fin N → Bool)).card = 2 ^ N := by
  simp

lemma card_good_ge (x : Fin N → W) (J : Finset (Fin N)) :
    (2:ℝ) ^ N ≤ 2 * ((Finset.univ.filter
      (fun ε : Fin N → Bool => ‖signedSum ε (zeroOn x J)‖ ≤ 2 * Eeps x)).card : ℝ) := by
  set A := Finset.univ.filter (fun ε : Fin N → Bool => ‖signedSum ε (zeroOn x J)‖ ≤ 2 * Eeps x) with hA
  set Ac := Finset.univ.filter (fun ε : Fin N → Bool => ¬ (‖signedSum ε (zeroOn x J)‖ ≤ 2 * Eeps x)) with hAc
  have hsplit : A.card + Ac.card = 2 ^ N := by
    rw [hA, hAc, Finset.card_filter_add_card_filter_not, card_univ_bool_fun]
  have hE := Eeps_zeroOn_le x J
  have hE0 := Eeps_nonneg (zeroOn x J)
  have hsum := sum_norm_signedSum (zeroOn x J)
  rcases eq_or_lt_of_le (Eeps_nonneg x) with h0 | hpos
  · -- Eeps x = 0: then every signed sum of x' vanishes
    have hE' : Eeps (zeroOn x J) = 0 := le_antisymm (by linarith) hE0
    have hall : ∀ ε ∈ (Finset.univ : Finset (Fin N → Bool)), ‖signedSum ε (zeroOn x J)‖ = 0 := by
      intro ε _
      have h := (Finset.sum_eq_zero_iff_of_nonneg (fun ε _ => norm_nonneg (signedSum ε (zeroOn x J)))).mp
        (by rw [hsum, hE', mul_zero]) ε (Finset.mem_univ ε)
      exact h
    have : A = Finset.univ := by
      rw [hA, Finset.filter_eq_self]
      intro ε hε; rw [hall ε hε, ← h0]; norm_num
    rw [this, card_univ_bool_fun]
    push_cast
    linarith [pow_pos (by norm_num : (0:ℝ) < 2) N]
  · -- Markov
    have hlow : (Ac.card : ℝ) * (2 * Eeps x) ≤ ∑ ε ∈ Ac, ‖signedSum ε (zeroOn x J)‖ := by
      have : ∑ ε ∈ Ac, (2 * Eeps x) ≤ ∑ ε ∈ Ac, ‖signedSum ε (zeroOn x J)‖ := by
        apply Finset.sum_le_sum
        intro ε hε
        rw [hAc, Finset.mem_filter] at hε
        exact le_of_lt (not_le.mp hε.2)
      simpa [Finset.sum_const, nsmul_eq_mul] using this
    have hup : ∑ ε ∈ Ac, ‖signedSum ε (zeroOn x J)‖ ≤ 2 ^ N * Eeps x := by
      calc ∑ ε ∈ Ac, ‖signedSum ε (zeroOn x J)‖ ≤ ∑ ε, ‖signedSum ε (zeroOn x J)‖ :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _ => norm_nonneg _)
        _ = 2 ^ N * Eeps (zeroOn x J) := hsum
        _ ≤ 2 ^ N * Eeps x := by gcongr
    have h1 : (Ac.card : ℝ) * 2 ≤ 2 ^ N := by
      have := hlow.trans hup
      nlinarith
    have h2 : (A.card : ℝ) + Ac.card = 2 ^ N := by exact_mod_cast hsplit
    linarith

theorem prop_13_3_core {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    {N : ℕ} (q : ℕ) (hq : 2 ≤ q) (b : ℝ) (hb : 0 < b)
    (x : Fin N → W) (u : ℝ) (hu : 0 < u) :
    Komlos.spMeasure N
        {ε | 2 * Eeps x + u + topSumE x (kSigma q b x) ≤ ‖signedSum ε x‖}
      ≤ ENNReal.ofReal (4 * Real.exp (-(u ^ 2 / (16 * q * b ^ 2)))) := by
  obtain ⟨y, hy, htop⟩ := topSumE_kSigma q hb x
  set J := mismatch q x y with hJ
  set x' := zeroOn x J with hx'
  set c : ℝ := Real.sqrt q * b with hcdef
  have hq0 : (0:ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  have hc : 0 < c := mul_pos (Real.sqrt_pos.mpr hq0) hb
  have hc2 : c ^ 2 = q * b ^ 2 := by rw [hcdef, mul_pow, Real.sq_sqrt hq0.le]
  set A := Finset.univ.filter (fun ε : Fin N → Bool => ‖signedSum ε x'‖ ≤ 2 * Eeps x) with hAdef
  have hA2 := card_good_ge x J
  have hAne : A.Nonempty := by
    rw [← Finset.card_pos]
    have h2 : (0:ℝ) < 2 ^ N := by positivity
    have : (0:ℝ) < A.card := by linarith
    exact_mod_cast this
  set r := u / (2 * c) with hr_def
  have hr : 0 ≤ r := by positivity
  have hkey : ∀ ε, ‖signedSum ε x'‖ ≤ 2 * Eeps x + 2 * c * dc A ε := by
    intro ε
    by_cases h0 : signedSum ε x' = 0
    · rw [h0, norm_zero]
      have := dc_nonneg A hAne ε; have := Eeps_nonneg x; positivity
    obtain ⟨w, hw1, hwv⟩ := exists_dual_vector ℝ _ (norm_ne_zero_iff.mpr h0)
    have hwv' : w (signedSum ε x') = ‖signedSum ε x'‖ := by simpa using hwv
    rw [← hwv']
    set α : Fin N → ℝ := fun i => |w (x' i)| / c with hαdef
    have hα : α ∈ Adm N := by
      refine ⟨fun i => by positivity, ?_⟩
      simp only [hαdef, div_pow, ← Finset.sum_div]
      rw [div_le_one (by positivity), hc2]
      simp only [sq_abs]
      exact sum_sq_zeroOn_le q hb x y hy hw1.le
    have hham : w (signedSum ε x') - 2 * Eeps x ≤ hamW A ((2 * c) • α) ε := by
      apply le_hamW A hAne
      intro ε' hε'
      rw [hAdef, Finset.mem_filter] at hε'
      have h := apply_signedSum_le x' ε ε' w hw1.le
      have e : ∑ i, ((2 * c) • α) i * dis ε ε' i = 2 * ∑ i, |w (x' i)| * dis ε ε' i := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl; intro i _
        simp only [hαdef, Pi.smul_apply, smul_eq_mul]
        field_simp
      rw [e]
      linarith [hε'.2]
    rw [hamW_smul A α ε (by positivity)] at hham
    have := hamW_le_dc A hα ε
    nlinarith
  have hsub : {ε | 2 * Eeps x + u + topSumE x (kSigma q b x) ≤ ‖signedSum ε x‖} ⊆ {ε | r ≤ dc A ε} := by
    intro ε hε
    simp only [Set.mem_setOf_eq] at hε ⊢
    have h1 := norm_signedSum_le_zeroOn ε x J
    have h2 := sum_norm_le_topSum x J.card J rfl
    rw [htop] at hε
    have h3 := hkey ε
    have : u ≤ 2 * c * dc A ε := by linarith
    rw [hr_def, div_le_iff₀ (by positivity)]; linarith
  calc Komlos.spMeasure N {ε | 2 * Eeps x + u + topSumE x (kSigma q b x) ≤ ‖signedSum ε x‖}
      ≤ Komlos.spMeasure N {ε | r ≤ dc A ε} := measure_mono hsub
    _ ≤ ENNReal.ofReal (2 * Real.exp (-(r ^ 2 / 4))) := spMeasure_dc_ge_le A hAne hA2 hr
    _ ≤ ENNReal.ofReal (4 * Real.exp (-(u ^ 2 / (16 * q * b ^ 2)))) := by
        apply ENNReal.ofReal_le_ofReal
        have e : r ^ 2 / 4 = u ^ 2 / (16 * q * b ^ 2) := by
          rw [hr_def, div_pow, mul_pow, hc2]; field_simp; ring
        rw [e]
        linarith [Real.exp_pos (-(u ^ 2 / (16 * q * b ^ 2)))]

end Main

end TalagrandConc.BanachSums

open TalagrandConc.BanachSums


theorem solution {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
    {N : ℕ} (q : ℕ) (hq : 2 ≤ q) (b : ℝ) (hb : 0 < b)
    (x : Fin N → W) (u : ℝ) (hu : 0 < u) :
    Komlos.spMeasure N
        {ε | 2 * Eeps x + u + topSumE x (kSigma q b x) ≤ ‖signedSum ε x‖}
      ≤ ENNReal.ofReal (4 * Real.exp (-(u ^ 2 / (16 * q * b ^ 2)))) := by
  exact prop_13_3_core q hq b hb x u hu
