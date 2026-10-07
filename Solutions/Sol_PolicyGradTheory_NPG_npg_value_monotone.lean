import Mathlib
import Definitions.Def_PolicyGradTheory_ProjGA_MDP
import Definitions.Def_PolicyGradTheory_NPG_Algorithm
import Definitions.Def_FoundationsML_ReinforcementLearning_IsOptimalPolicy

open FoundationsML.ReinforcementLearning


namespace PolicyGradTheory.NPG

section MDP
variable {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A]

/-- induced transition matrix -/
noncomputable def npgM (π : S → A → ℝ) (P : S → A → S → ℝ) : Matrix S S ℝ :=
  Matrix.of fun s s' => InducedTransition π P s s'

lemma npg_occ_eq_pow (π : S → A → ℝ) (P : S → A → S → ℝ) (s0 : S) (t : ℕ) (s : S) :
    OccupationDist π P s0 t s = (npgM π P ^ t) s0 s := by
  induction t generalizing s with
  | zero => simp [OccupationDist, Matrix.one_apply, eq_comm]
  | succ t ih =>
    simp only [OccupationDist, pow_succ, Matrix.mul_apply, ih]
    rfl

variable {π : S → A → ℝ} {P : S → A → S → ℝ}

lemma npg_M_nonneg (hP : IsTransitionKernel P) (hπ : IsPolicy π) (s s' : S) :
    0 ≤ npgM π P s s' := by
  simp only [npgM, Matrix.of_apply, InducedTransition]
  exact Finset.sum_nonneg fun a _ => mul_nonneg ((hπ s).1 a) ((hP s a).1 s')

lemma npg_M_rowsum (hP : IsTransitionKernel P) (hπ : IsPolicy π) (s : S) :
    ∑ s', npgM π P s s' = 1 := by
  simp only [npgM, Matrix.of_apply, InducedTransition]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, (hP s _).2, mul_one]
  exact (hπ s).2

lemma npg_pow_nonneg (hP : IsTransitionKernel P) (hπ : IsPolicy π) (t : ℕ) (s s' : S) :
    0 ≤ (npgM π P ^ t) s s' := by
  induction t generalizing s' with
  | zero => simp [Matrix.one_apply]; split_ifs <;> norm_num
  | succ t ih =>
    rw [pow_succ, Matrix.mul_apply]
    exact Finset.sum_nonneg fun x _ => mul_nonneg (ih x) (npg_M_nonneg hP hπ x s')

lemma npg_pow_rowsum (hP : IsTransitionKernel P) (hπ : IsPolicy π) (t : ℕ) (s : S) :
    ∑ s', (npgM π P ^ t) s s' = 1 := by
  induction t with
  | zero => simp [Matrix.one_apply]
  | succ t ih =>
    simp_rw [pow_succ, Matrix.mul_apply]
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, npg_M_rowsum hP hπ, mul_one]
    exact ih

lemma npg_pow_le_one (hP : IsTransitionKernel P) (hπ : IsPolicy π) (t : ℕ) (s s' : S) :
    (npgM π P ^ t) s s' ≤ 1 := by
  rw [← npg_pow_rowsum hP hπ t s]
  exact Finset.single_le_sum (fun x _ => npg_pow_nonneg hP hπ t s x) (Finset.mem_univ _)

lemma npg_E_bound (hP : IsTransitionKernel P) (hπ : IsPolicy π) (t : ℕ) (s : S) (g : S → ℝ)
    (B : ℝ) (hg : ∀ x, |g x| ≤ B) : |∑ s', (npgM π P ^ t) s s' * g s'| ≤ B := by
  calc |∑ s', (npgM π P ^ t) s s' * g s'| ≤ ∑ s', |(npgM π P ^ t) s s' * g s'| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ s', (npgM π P ^ t) s s' * B := by
        apply Finset.sum_le_sum; intro x _
        rw [abs_mul, abs_of_nonneg (npg_pow_nonneg hP hπ t s x)]
        exact mul_le_mul_of_nonneg_left (hg x) (npg_pow_nonneg hP hπ t s x)
    _ = B := by rw [← Finset.sum_mul, npg_pow_rowsum hP hπ, one_mul]

lemma npg_summable (hP : IsTransitionKernel P) (hπ : IsPolicy π) {γ : ℝ} (hγ0 : 0 ≤ γ)
    (hγ1 : γ < 1) (s : S) (g : S → ℝ) (B : ℝ) (hg : ∀ x, |g x| ≤ B) :
    Summable (fun t : ℕ => γ ^ t * ∑ s', (npgM π P ^ t) s s' * g s') := by
  refine Summable.of_norm_bounded ((summable_geometric_of_lt_one hγ0 hγ1).mul_right B) ?_
  intro t
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hγ0 t)]
  exact mul_le_mul_of_nonneg_left (npg_E_bound hP hπ t s g B hg) (pow_nonneg hγ0 t)

lemma npg_tsum_bound (hP : IsTransitionKernel P) (hπ : IsPolicy π) {γ : ℝ} (hγ0 : 0 ≤ γ)
    (hγ1 : γ < 1) (s : S) (g : S → ℝ) (B : ℝ) (hg : ∀ x, |g x| ≤ B) :
    |∑' t : ℕ, γ ^ t * ∑ s', (npgM π P ^ t) s s' * g s'| ≤ B / (1 - γ) := by
  have hs := npg_summable hP hπ hγ0 hγ1 s g B hg
  have hgeo := (summable_geometric_of_lt_one hγ0 hγ1).mul_right B
  rw [← Real.norm_eq_abs]
  refine (norm_tsum_le_tsum_norm hs.norm).trans ?_
  calc ∑' t : ℕ, ‖γ ^ t * ∑ s', (npgM π P ^ t) s s' * g s'‖ ≤ ∑' t : ℕ, γ ^ t * B := by
        refine hs.norm.tsum_le_tsum (fun t => ?_) hgeo
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hγ0 t)]
        exact mul_le_mul_of_nonneg_left (npg_E_bound hP hπ t s g B hg) (pow_nonneg hγ0 t)
    _ = B / (1 - γ) := by rw [tsum_mul_right, tsum_geometric_of_lt_one hγ0 hγ1]; ring

lemma npg_value_eq (π : S → A → ℝ) (P : S → A → S → ℝ) (r : S → A → ℝ) (γ : ℝ) (s : S) :
    PolicyValue π P r γ s =
      ∑' t : ℕ, γ ^ t * ∑ s', (npgM π P ^ t) s s' * InducedReward π r s' := by
  simp only [PolicyValue, npg_occ_eq_pow]

lemma npg_reward_bound (hπ : IsPolicy π) {r : S → A → ℝ} (hr : ∀ s a, 0 ≤ r s a ∧ r s a ≤ 1)
    (s : S) : |InducedReward π r s| ≤ 1 := by
  have h0 : 0 ≤ InducedReward π r s :=
    Finset.sum_nonneg fun a _ => mul_nonneg ((hπ s).1 a) (hr s a).1
  have h1 : InducedReward π r s ≤ 1 := by
    calc InducedReward π r s ≤ ∑ a, π s a * 1 :=
          Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_left (hr s a).2 ((hπ s).1 a)
      _ = 1 := by simp [(hπ s).2]
  rw [abs_le]; constructor <;> linarith

lemma npg_value_bound (hP : IsTransitionKernel P) (hπ : IsPolicy π) {r : S → A → ℝ}
    (hr : ∀ s a, 0 ≤ r s a ∧ r s a ≤ 1) {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (s : S) :
    |PolicyValue π P r γ s| ≤ 1 / (1 - γ) := by
  rw [npg_value_eq]
  exact npg_tsum_bound hP hπ hγ0 hγ1 s _ 1 (npg_reward_bound hπ hr)

/-- first-step identity for E -/
lemma npg_E_succ (π : S → A → ℝ) (P : S → A → S → ℝ) (t : ℕ) (s : S) (g : S → ℝ) :
    ∑ s', (npgM π P ^ (t + 1)) s s' * g s' =
      ∑ x, npgM π P s x * ∑ s', (npgM π P ^ t) x s' * g s' := by
  simp_rw [pow_succ', Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]; congr 1; ext x; congr 1; ext y; ring

lemma npg_E_succ' (π : S → A → ℝ) (P : S → A → S → ℝ) (t : ℕ) (s : S) (g : S → ℝ) :
    ∑ s', (npgM π P ^ (t + 1)) s s' * g s' =
      ∑ x, (npgM π P ^ t) s x * ∑ s', npgM π P x s' * g s' := by
  simp_rw [pow_succ, Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]; congr 1; ext x; congr 1; ext y; ring

/-- generic Bellman-type identity -/
lemma npg_tsum_bellman (hP : IsTransitionKernel P) (hπ : IsPolicy π) {γ : ℝ} (hγ0 : 0 ≤ γ)
    (hγ1 : γ < 1) (s : S) (g : S → ℝ) (B : ℝ) (hg : ∀ x, |g x| ≤ B) :
    ∑' t : ℕ, γ ^ t * ∑ s', (npgM π P ^ t) s s' * g s' =
      g s + γ * ∑ x, npgM π P s x * ∑' t : ℕ, γ ^ t * ∑ s', (npgM π P ^ t) x s' * g s' := by
  rw [(npg_summable hP hπ hγ0 hγ1 s g B hg).tsum_eq_zero_add]
  congr 1
  · simp [Matrix.one_apply]
  · simp_rw [npg_E_succ]
    have : ∀ t : ℕ, γ ^ (t + 1) * ∑ x, npgM π P s x * ∑ s', (npgM π P ^ t) x s' * g s' =
        ∑ x, (γ * npgM π P s x) * (γ ^ t * ∑ s', (npgM π P ^ t) x s' * g s') := by
      intro t; rw [Finset.mul_sum]; congr 1; ext x; ring
    simp_rw [this]
    rw [Summable.tsum_finsetSum (fun x _ =>
      (npg_summable hP hπ hγ0 hγ1 x g B hg).mul_left (γ * npgM π P s x))]
    rw [Finset.mul_sum]; congr 1; ext x
    rw [Summable.tsum_mul_left _ (npg_summable hP hπ hγ0 hγ1 x g B hg)]; ring

lemma npg_bellman (hP : IsTransitionKernel P) (hπ : IsPolicy π) {r : S → A → ℝ}
    (hr : ∀ s a, 0 ≤ r s a ∧ r s a ≤ 1) {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (s : S) :
    PolicyValue π P r γ s =
      InducedReward π r s + γ * ∑ x, npgM π P s x * PolicyValue π P r γ x := by
  simp_rw [npg_value_eq]
  exact npg_tsum_bellman hP hπ hγ0 hγ1 s _ 1 (npg_reward_bound hπ hr)

lemma npg_adv_sum (hP : IsTransitionKernel P) (hπ : IsPolicy π) {r : S → A → ℝ}
    (hr : ∀ s a, 0 ≤ r s a ∧ r s a ≤ 1) {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (π' : S → A → ℝ)
    (s : S) :
    ∑ a, π' s a * PolicyGradTheory.ProjGA.advantage π P r γ s a =
      InducedReward π' r s + γ * ∑ x, npgM π' P s x * PolicyValue π P r γ x
        - (∑ a, π' s a) * PolicyValue π P r γ s := by
  simp only [PolicyGradTheory.ProjGA.advantage, QFunction, InducedReward, npgM, Matrix.of_apply,
    InducedTransition, mul_sub, Finset.sum_sub_distrib, mul_add, Finset.sum_add_distrib,
    Finset.sum_mul, Finset.mul_sum]
  congr 1; congr 1
  rw [Finset.sum_comm]; congr 1; ext a; congr 1; ext x; ring

lemma npg_adv_sum_self (hP : IsTransitionKernel P) (hπ : IsPolicy π) {r : S → A → ℝ}
    (hr : ∀ s a, 0 ≤ r s a ∧ r s a ≤ 1) {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (s : S) :
    ∑ a, π s a * PolicyGradTheory.ProjGA.advantage π P r γ s a = 0 := by
  rw [npg_adv_sum hP hπ hr hγ0 hγ1, (hπ s).2, ← npg_bellman hP hπ hr hγ0 hγ1]; ring


lemma npg_pdl_state (hP : IsTransitionKernel P) (hπ : IsPolicy π) {π' : S → A → ℝ}
    (hπ' : IsPolicy π') {r : S → A → ℝ}
    (hr : ∀ s a, 0 ≤ r s a ∧ r s a ≤ 1) {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (s0 : S) :
    PolicyValue π P r γ s0 - PolicyValue π' P r γ s0 =
      ∑' t : ℕ, γ ^ t * ∑ s', (npgM π P ^ t) s0 s' *
        (∑ a, π s' a * PolicyGradTheory.ProjGA.advantage π' P r γ s' a) := by
  have hVb : ∀ x, |PolicyValue π' P r γ x| ≤ 1 / (1 - γ) :=
    fun x => npg_value_bound hP hπ' hr hγ0 hγ1 x
  have hbs : Summable (fun t : ℕ => γ ^ t * ∑ s', (npgM π P ^ t) s0 s' * PolicyValue π' P r γ s') :=
    npg_summable hP hπ hγ0 hγ1 s0 _ _ hVb
  have has : Summable (fun t : ℕ => γ ^ t * ∑ s', (npgM π P ^ t) s0 s' * InducedReward π r s') :=
    npg_summable hP hπ hγ0 hγ1 s0 _ 1 (npg_reward_bound hπ hr)
  have hbs1 : Summable (fun t : ℕ => γ ^ (t + 1) * ∑ s', (npgM π P ^ (t + 1)) s0 s' *
      PolicyValue π' P r γ s') := hbs.comp_injective (add_left_injective 1)
  have hterm : ∀ t : ℕ, γ ^ t * ∑ s', (npgM π P ^ t) s0 s' *
        (∑ a, π s' a * PolicyGradTheory.ProjGA.advantage π' P r γ s' a) =
      (γ ^ t * ∑ s', (npgM π P ^ t) s0 s' * InducedReward π r s') +
        (γ ^ (t + 1) * ∑ s', (npgM π P ^ (t + 1)) s0 s' * PolicyValue π' P r γ s') -
        (γ ^ t * ∑ s', (npgM π P ^ t) s0 s' * PolicyValue π' P r γ s') := by
    intro t
    simp_rw [npg_adv_sum hP hπ' hr hγ0 hγ1 π, (hπ _).2, one_mul]
    rw [npg_E_succ']
    simp only [mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib, pow_succ]
    simp_rw [Finset.mul_sum]
    ring_nf
  rw [tsum_congr hterm, Summable.tsum_sub (has.add hbs1) hbs, Summable.tsum_add has hbs1,
    hbs.tsum_eq_zero_add, npg_value_eq π P r γ s0]
  simp [Matrix.one_apply]

/-- sums against the visitation distribution -/
lemma npg_vis_sum (hP : IsTransitionKernel P) (hπ : IsPolicy π) {γ : ℝ} (hγ0 : 0 ≤ γ)
    (hγ1 : γ < 1) (ρ : S → ℝ) (f : S → ℝ) (B : ℝ) (hf : ∀ x, |f x| ≤ B) :
    ∑ s, PolicyGradTheory.ProjGA.visitation π P γ ρ s * f s =
      (1 - γ) * ∑ s0, ρ s0 * ∑' t : ℕ, γ ^ t * ∑ s', (npgM π P ^ t) s0 s' * f s' := by
  have hu : ∀ s, Summable (fun t : ℕ => γ ^ t * ∑ s0, ρ s0 * (npgM π P ^ t) s0 s) := by
    intro s
    refine Summable.of_norm_bounded
      ((summable_geometric_of_lt_one hγ0 hγ1).mul_right (∑ s0, |ρ s0|)) ?_
    intro t
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hγ0 t)]
    refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg hγ0 t)
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun x _ => ?_)
    rw [abs_mul, abs_of_nonneg (npg_pow_nonneg hP hπ t x s)]
    exact mul_le_of_le_one_right (abs_nonneg _) (npg_pow_le_one hP hπ t x s)
  simp only [PolicyGradTheory.ProjGA.visitation, npg_occ_eq_pow]
  have h1 : ∀ s, (1 - γ) * (∑' t : ℕ, γ ^ t * ∑ s0, ρ s0 * (npgM π P ^ t) s0 s) * f s =
      (1 - γ) * ∑' t : ℕ, γ ^ t * ∑ s0, ρ s0 * (npgM π P ^ t) s0 s * f s := by
    intro s
    rw [mul_assoc, ← (hu s).tsum_mul_right]
    congr 2; ext t; rw [mul_assoc, Finset.sum_mul]
  simp_rw [h1]
  rw [← Finset.mul_sum, ← Summable.tsum_finsetSum]
  · congr 1
    have h2 : ∀ t : ℕ, ∑ s, γ ^ t * ∑ s0, ρ s0 * (npgM π P ^ t) s0 s * f s =
        ∑ s0, ρ s0 * (γ ^ t * ∑ s', (npgM π P ^ t) s0 s' * f s') := by
      intro t
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]; congr 1; ext x; congr 1; ext y; ring
    simp_rw [h2]
    rw [Summable.tsum_finsetSum]
    · congr 1; ext s0
      exact Summable.tsum_mul_left _ (npg_summable hP hπ hγ0 hγ1 s0 f B hf)
    · intro s0 _
      exact (npg_summable hP hπ hγ0 hγ1 s0 f B hf).mul_left _
  · intro s _
    have := (hu s).mul_right (f s)
    refine this.congr fun t => ?_
    rw [mul_assoc, Finset.sum_mul]

lemma npg_adv_bound (hP : IsTransitionKernel P) (hπ : IsPolicy π) {π' : S → A → ℝ}
    (hπ' : IsPolicy π') {r : S → A → ℝ}
    (hr : ∀ s a, 0 ≤ r s a ∧ r s a ≤ 1) {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (s : S) :
    |∑ a, π s a * PolicyGradTheory.ProjGA.advantage π' P r γ s a| ≤ 1 + 2 / (1 - γ) := by
  rw [npg_adv_sum hP hπ' hr hγ0 hγ1 π, (hπ s).2, one_mul]
  have h1 := npg_reward_bound hπ hr s
  have h2 := npg_E_bound (t := 1) hP hπ s (fun x => PolicyValue π' P r γ x) _
    (fun x => npg_value_bound hP hπ' hr hγ0 hγ1 x)
  simp only [pow_one] at h2
  have h3 := npg_value_bound hP hπ' hr hγ0 hγ1 s
  have hg : 0 < 1 - γ := by linarith
  have h4 : |γ * ∑ x, npgM π P s x * PolicyValue π' P r γ x| ≤ 1 / (1 - γ) := by
    rw [abs_mul, abs_of_nonneg hγ0]
    calc γ * _ ≤ 1 * (1 / (1 - γ)) := mul_le_mul (by linarith) h2 (abs_nonneg _) (by norm_num)
      _ = _ := one_mul _
  calc _ ≤ |InducedReward π r s + γ * ∑ x, npgM π P s x * PolicyValue π' P r γ x|
        + |PolicyValue π' P r γ s| := abs_sub _ _
    _ ≤ |InducedReward π r s| + |γ * ∑ x, npgM π P s x * PolicyValue π' P r γ x|
        + |PolicyValue π' P r γ s| := by gcongr; exact abs_add_le _ _
    _ ≤ 1 + 1 / (1 - γ) + 1 / (1 - γ) := by gcongr
    _ = _ := by ring

/-- performance difference lemma with a general start vector `ρ` -/
lemma npg_pdl (hP : IsTransitionKernel P) (hπ : IsPolicy π) {π' : S → A → ℝ}
    (hπ' : IsPolicy π') {r : S → A → ℝ}
    (hr : ∀ s a, 0 ≤ r s a ∧ r s a ≤ 1) {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (ρ : S → ℝ) :
    PolicyGradTheory.ProjGA.valueAt π P r γ ρ - PolicyGradTheory.ProjGA.valueAt π' P r γ ρ =
      1 / (1 - γ) * ∑ s, PolicyGradTheory.ProjGA.visitation π P γ ρ s *
        ∑ a, π s a * PolicyGradTheory.ProjGA.advantage π' P r γ s a := by
  rw [npg_vis_sum hP hπ hγ0 hγ1 ρ _ _ (npg_adv_bound hP hπ hπ' hr hγ0 hγ1)]
  have hg : (1 - γ) ≠ 0 := by linarith
  rw [← mul_assoc, one_div_mul_cancel hg, one_mul]
  simp only [PolicyGradTheory.ProjGA.valueAt, ← Finset.sum_sub_distrib, ← mul_sub]
  congr 1; ext s0
  rw [npg_pdl_state hP hπ hπ' hr hγ0 hγ1]

end MDP

section SM
variable {S A : Type*} [Fintype S] [Fintype A]

lemma npg_Z_pos [Nonempty A] (θ : EuclideanSpace ℝ (S × A)) (s : S) :
    0 < ∑ b, Real.exp (θ (s, b)) :=
  Finset.sum_pos (fun b _ => Real.exp_pos _) Finset.univ_nonempty

lemma npg_sm_pos [Nonempty A] (θ : EuclideanSpace ℝ (S × A)) (s : S) (a : A) :
    0 < softmaxPolicy θ s a :=
  div_pos (Real.exp_pos _) (npg_Z_pos θ s)

lemma npg_sm_sum [Nonempty A] (θ : EuclideanSpace ℝ (S × A)) (s : S) :
    ∑ a, softmaxPolicy θ s a = 1 := by
  simp only [softmaxPolicy, ← Finset.sum_div]
  exact div_self (npg_Z_pos θ s).ne'

lemma npg_sm_policy [Nonempty A] (θ : EuclideanSpace ℝ (S × A)) : IsPolicy (softmaxPolicy θ) :=
  fun s => ⟨fun a => (npg_sm_pos θ s a).le, npg_sm_sum θ s⟩

lemma npg_sm_cont [Nonempty A] (s : S) (a : A) :
    Continuous (fun θ : EuclideanSpace ℝ (S × A) => softmaxPolicy θ s a) := by
  have hp : ∀ i : S × A, Continuous (fun θ : EuclideanSpace ℝ (S × A) => θ i) :=
    fun i => (EuclideanSpace.proj (𝕜 := ℝ) i).continuous
  simp only [softmaxPolicy]
  exact ((hp _).rexp).div (continuous_finset_sum _ fun b _ => (hp _).rexp)
    (fun θ => (npg_Z_pos θ s).ne')

/-- derivative of log-softmax -/
noncomputable def npgDL (θ : EuclideanSpace ℝ (S × A)) (s : S) (a : A) :
    EuclideanSpace ℝ (S × A) →L[ℝ] ℝ :=
  EuclideanSpace.proj (s, a) - ∑ b, softmaxPolicy θ s b • EuclideanSpace.proj (s, b)

lemma npgDL_apply (θ h : EuclideanSpace ℝ (S × A)) (s : S) (a : A) :
    npgDL θ s a h = h (s, a) - ∑ b, softmaxPolicy θ s b * h (s, b) := by
  simp [npgDL]

lemma npg_lsm_eq [Nonempty A] (θ : EuclideanSpace ℝ (S × A)) (s : S) (a : A) :
    Real.log (softmaxPolicy θ s a) = θ (s, a) - Real.log (∑ b, Real.exp (θ (s, b))) := by
  simp only [softmaxPolicy]
  rw [Real.log_div (Real.exp_pos _).ne' (npg_Z_pos θ s).ne', Real.log_exp]

lemma npg_lsm_hasFDeriv [Nonempty A] (θ : EuclideanSpace ℝ (S × A)) (s : S) (a : A) :
    HasFDerivAt (fun θ' : EuclideanSpace ℝ (S × A) => Real.log (softmaxPolicy θ' s a))
      (npgDL θ s a) θ := by
  have hp : ∀ i : S × A, HasFDerivAt (fun θ : EuclideanSpace ℝ (S × A) => θ i)
      (EuclideanSpace.proj (𝕜 := ℝ) i) θ := fun i => by
    convert (EuclideanSpace.proj (𝕜 := ℝ) i).hasFDerivAt (x := θ) using 1
    funext x; rfl
  simp_rw [npg_lsm_eq]
  have hZ : HasFDerivAt (fun θ' : EuclideanSpace ℝ (S × A) => ∑ b, Real.exp (θ' (s, b)))
      (∑ b, Real.exp (θ (s, b)) • EuclideanSpace.proj (𝕜 := ℝ) (s, b)) θ :=
    HasFDerivAt.fun_sum (u := Finset.univ) (fun b _ => (hp (s, b)).exp)
  have := (hp (s, a)).sub (hZ.log (npg_Z_pos θ s).ne')
  refine this.congr_fderiv ?_
  ext h
  simp only [npgDL, ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.coe_sum', Finset.sum_apply, smul_eq_mul, softmaxPolicy]
  congr 1
  rw [Finset.mul_sum]; congr 1; ext b
  field_simp

lemma npg_sm_hasFDeriv [Nonempty A] (θ : EuclideanSpace ℝ (S × A)) (s : S) (a : A) :
    HasFDerivAt (fun θ' : EuclideanSpace ℝ (S × A) => softmaxPolicy θ' s a)
      (softmaxPolicy θ s a • npgDL θ s a) θ := by
  have h := (npg_lsm_hasFDeriv θ s a).exp
  simp only [Real.exp_log (npg_sm_pos _ s a)] at h
  exact h

/-- the score vector -/
lemma npg_score_eq [DecidableEq S] [DecidableEq A] [Nonempty A] (θ : EuclideanSpace ℝ (S × A))
    (s : S) (a : A) (i : S × A) :
    scoreVec θ s a i = if i.1 = s then ((if i.2 = a then 1 else 0) - softmaxPolicy θ s i.2) else 0 := by
  have hg : HasGradientAt (fun θ' : EuclideanSpace ℝ (S × A) => Real.log (softmaxPolicy θ' s a))
      (WithLp.toLp 2 (fun i : S × A =>
        if i.1 = s then ((if i.2 = a then 1 else 0) - softmaxPolicy θ s i.2) else 0)) θ := by
    rw [hasGradientAt_iff_hasFDerivAt]
    refine (npg_lsm_hasFDeriv θ s a).congr_fderiv ?_
    ext h
    rw [npgDL_apply, InnerProductSpace.toDual_apply_apply]
    simp only [PiLp.inner_apply, Fintype.sum_prod_type, RCLike.inner_apply,
      conj_trivial]
    simp [ite_mul, sub_mul, Finset.sum_sub_distrib, mul_comm]
  unfold scoreVec
  rw [hg.gradient]

end SM

section Grad
variable {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A] [DecidableEq A]

open Filter Asymptotics Topology in
lemma npg_prod_deriv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {c φ : E → ℝ}
    {φ' : E →L[ℝ] ℝ} {x : E} (hc : ContinuousAt c x) (hφ : HasFDerivAt φ φ' x) (h0 : φ x = 0) :
    HasFDerivAt (fun y => c y * φ y) (c x • φ') x := by
  apply HasFDerivAt.of_isLittleO
  have h1 : (fun y => c x * (φ y - φ x - φ' (y - x))) =o[𝓝 x] (fun y => y - x) :=
    hφ.isLittleO.const_mul_left (c x)
  have hc0 : (fun y => c y - c x) =o[𝓝 x] (fun _ => (1 : ℝ)) := by
    rw [isLittleO_one_iff]
    have := hc.tendsto.sub_const (c x)
    simpa using this
  have h2 : (fun y => (c y - c x) * (φ y - φ x)) =o[𝓝 x] (fun y => (1 : ℝ) * ‖y - x‖) :=
    hc0.mul_isBigO hφ.isBigO_sub.norm_right
  simp only [one_mul] at h2
  have h3 := (h1.add (isLittleO_norm_right.mp h2))
  refine h3.congr_left fun y => ?_
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul, h0]
  ring

lemma npg_occ_cont [Nonempty A] (P : S → A → S → ℝ) (s0 : S) (t : ℕ) (s : S) :
    Continuous (fun θ : EuclideanSpace ℝ (S × A) => OccupationDist (softmaxPolicy θ) P s0 t s) := by
  induction t generalizing s with
  | zero => exact continuous_const
  | succ t ih =>
    simp only [OccupationDist, InducedTransition]
    exact continuous_finsetSum _ fun x _ => (ih x).mul
      (continuous_finsetSum _ fun a _ => (npg_sm_cont x a).mul continuous_const)

lemma npg_vis_cont [Nonempty A] {P : S → A → S → ℝ} (hP : IsTransitionKernel P) {γ : ℝ}
    (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (ρ : S → ℝ) (s : S) :
    Continuous (fun θ : EuclideanSpace ℝ (S × A) =>
      PolicyGradTheory.ProjGA.visitation (softmaxPolicy θ) P γ ρ s) := by
  unfold PolicyGradTheory.ProjGA.visitation
  refine continuous_const.mul (continuous_tsum (fun t => ?_)
    ((summable_geometric_of_lt_one hγ0 hγ1).mul_right (∑ s0, |ρ s0|)) (fun t θ => ?_))
  · exact continuous_const.mul (continuous_finsetSum _ fun s0 _ =>
      continuous_const.mul (npg_occ_cont P s0 t s))
  · rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hγ0 t)]
    refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg hγ0 t)
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun x _ => ?_)
    rw [npg_occ_eq_pow, abs_mul, abs_of_nonneg (npg_pow_nonneg hP (npg_sm_policy θ) t x s)]
    exact mul_le_of_le_one_right (abs_nonneg _) (npg_pow_le_one hP (npg_sm_policy θ) t x s)

/-- the policy gradient theorem for the softmax parameterization -/
lemma npg_valueGrad_eq [Nonempty A] {P : S → A → S → ℝ} {r : S → A → ℝ} {γ : ℝ}
    (hM : PolicyGradTheory.ProjGA.IsFiniteMDP P r γ) (ρ : S → ℝ) (θ : EuclideanSpace ℝ (S × A)) :
    valueGrad P r γ ρ θ = WithLp.toLp 2 (fun i : S × A =>
      1 / (1 - γ) * PolicyGradTheory.ProjGA.visitation (softmaxPolicy θ) P γ ρ i.1 *
        (softmaxPolicy θ i.1 i.2 *
          PolicyGradTheory.ProjGA.advantage (softmaxPolicy θ) P r γ i.1 i.2)) := by
  obtain ⟨hP, hr, hγ0, hγ1⟩ := hM
  set π := softmaxPolicy θ with hπdef
  have hπ : IsPolicy π := npg_sm_policy θ
  -- the identity from the performance difference lemma
  have hid : (fun θ' : EuclideanSpace ℝ (S × A) =>
      PolicyGradTheory.ProjGA.valueAt (softmaxPolicy θ') P r γ ρ) = fun θ' =>
      PolicyGradTheory.ProjGA.valueAt π P r γ ρ + ∑ s, 1 / (1 - γ) *
        (PolicyGradTheory.ProjGA.visitation (softmaxPolicy θ') P γ ρ s *
          ∑ a, softmaxPolicy θ' s a * PolicyGradTheory.ProjGA.advantage π P r γ s a) := by
    funext θ'
    have := npg_pdl hP (npg_sm_policy θ') hπ hr hγ0 hγ1 ρ
    rw [← Finset.mul_sum, ← this]; ring
  have hφ : ∀ s, HasFDerivAt (fun θ' : EuclideanSpace ℝ (S × A) =>
      ∑ a, softmaxPolicy θ' s a * PolicyGradTheory.ProjGA.advantage π P r γ s a)
      (∑ a, PolicyGradTheory.ProjGA.advantage π P r γ s a • (π s a • npgDL θ s a)) θ :=
    fun s => HasFDerivAt.fun_sum fun a _ => (npg_sm_hasFDeriv θ s a).mul_const _
  have hφ0 : ∀ s, ∑ a, softmaxPolicy θ s a * PolicyGradTheory.ProjGA.advantage π P r γ s a = 0 :=
    fun s => npg_adv_sum_self hP hπ hr hγ0 hγ1 s
  have hD := (HasFDerivAt.fun_sum (u := Finset.univ) fun s _ =>
    (npg_prod_deriv ((npg_vis_cont hP hγ0 hγ1 ρ s).continuousAt) (hφ s) (hφ0 s)).const_mul
      (1 / (1 - γ))).const_add (PolicyGradTheory.ProjGA.valueAt π P r γ ρ)
  rw [← hid] at hD
  have hG : HasGradientAt (fun θ' : EuclideanSpace ℝ (S × A) =>
      PolicyGradTheory.ProjGA.valueAt (softmaxPolicy θ') P r γ ρ) (WithLp.toLp 2 (fun i : S × A =>
      1 / (1 - γ) * PolicyGradTheory.ProjGA.visitation (softmaxPolicy θ) P γ ρ i.1 *
        (softmaxPolicy θ i.1 i.2 *
          PolicyGradTheory.ProjGA.advantage (softmaxPolicy θ) P r γ i.1 i.2))) θ := by
    rw [hasGradientAt_iff_hasFDerivAt]
    refine hD.congr_fderiv ?_
    ext h
    rw [InnerProductSpace.toDual_apply_apply]
    simp only [PiLp.inner_apply, Fintype.sum_prod_type, RCLike.inner_apply, conj_trivial,
      ContinuousLinearMap.coe_sum', Finset.sum_apply, ContinuousLinearMap.smul_apply,
      smul_eq_mul, npgDL_apply]
    congr 1; ext s
    have h0 := hφ0 s
    simp only [mul_sub, Finset.sum_sub_distrib]
    rw [← hπdef] at h0 ⊢
    have : ∑ a, PolicyGradTheory.ProjGA.advantage π P r γ s a *
        (π s a * ∑ b, π s b * h (s, b)) = 0 := by
      simp_rw [← mul_assoc, ← Finset.sum_mul]
      rw [show ∑ a, PolicyGradTheory.ProjGA.advantage π P r γ s a * π s a = 0 by
        rw [← h0]; congr 1; ext a; ring]
      ring
    rw [this, mul_zero, mul_zero, sub_zero, Finset.mul_sum, Finset.mul_sum]
    congr 1; ext a; ring
  exact hG.gradient

end Grad

section Fisher
variable {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A] [DecidableEq A]

lemma npg_pow_pos_transfer {P : S → A → S → ℝ} (hP : IsTransitionKernel P) {π π' : S → A → ℝ}
    (hπ : IsPolicy π) (hpos : ∀ s a, 0 < π s a) (t : ℕ) (s0 s : S)
    (h : (npgM π' P ^ t) s0 s ≠ 0) : 0 < (npgM π P ^ t) s0 s := by
  induction t generalizing s with
  | zero =>
    simp only [pow_zero, Matrix.one_apply] at h ⊢
    split_ifs at h ⊢ <;> simp_all
  | succ t ih =>
    rw [pow_succ, Matrix.mul_apply] at h ⊢
    obtain ⟨x, -, hx⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
    have h1 : (npgM π' P ^ t) s0 x ≠ 0 := left_ne_zero_of_mul hx
    have h2 : npgM π' P x s ≠ 0 := right_ne_zero_of_mul hx
    simp only [npgM, Matrix.of_apply, InducedTransition] at h2
    obtain ⟨a, -, ha⟩ := Finset.exists_ne_zero_of_sum_ne_zero h2
    have hPa : 0 < P x a s := lt_of_le_of_ne ((hP x a).1 s) (Ne.symm (right_ne_zero_of_mul ha))
    have hM : 0 < npgM π P x s := by
      simp only [npgM, Matrix.of_apply, InducedTransition]
      calc 0 < π x a * P x a s := mul_pos (hpos x a) hPa
        _ ≤ ∑ a', π x a' * P x a' s :=
          Finset.single_le_sum (f := fun a' => π x a' * P x a' s)
            (fun a' _ => mul_nonneg ((hπ x).1 a') ((hP x a').1 s)) (Finset.mem_univ a)
    calc 0 < (npgM π P ^ t) s0 x * npgM π P x s := mul_pos (ih x h1) hM
      _ ≤ ∑ y, (npgM π P ^ t) s0 y * npgM π P y s :=
          Finset.single_le_sum (f := fun y => (npgM π P ^ t) s0 y * npgM π P y s)
            (fun y _ => mul_nonneg (npg_pow_nonneg hP hπ t s0 y) (npg_M_nonneg hP hπ y s))
            (Finset.mem_univ x)

lemma npg_vis_pos_of {P : S → A → S → ℝ} (hP : IsTransitionKernel P) {π π' : S → A → ℝ}
    (hπ : IsPolicy π) (hpos : ∀ s a, 0 < π s a) {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (ρ : S → ℝ) (hρ0 : ∀ x, 0 ≤ ρ x) (s : S)
    (h : 0 < PolicyGradTheory.ProjGA.visitation π' P γ ρ s) :
    0 < PolicyGradTheory.ProjGA.visitation π P γ ρ s := by
  unfold PolicyGradTheory.ProjGA.visitation at h ⊢
  simp only [npg_occ_eq_pow] at h ⊢
  have hT : (∑' t : ℕ, γ ^ t * ∑ s0, ρ s0 * (npgM π' P ^ t) s0 s) ≠ 0 := by
    intro h0; rw [h0, mul_zero] at h; exact lt_irrefl _ h
  obtain ⟨t, ht⟩ : ∃ t : ℕ, γ ^ t * ∑ s0, ρ s0 * (npgM π' P ^ t) s0 s ≠ 0 := by
    by_contra hc
    push_neg at hc
    apply hT
    simp [hc]
  have hγt : 0 < γ ^ t := lt_of_le_of_ne (pow_nonneg hγ0 t) (Ne.symm (left_ne_zero_of_mul ht))
  obtain ⟨s0, -, hs0⟩ := Finset.exists_ne_zero_of_sum_ne_zero (right_ne_zero_of_mul ht)
  have hρs : 0 < ρ s0 := lt_of_le_of_ne (hρ0 s0) (Ne.symm (left_ne_zero_of_mul hs0))
  have hMs := npg_pow_pos_transfer hP hπ hpos t s0 s (right_ne_zero_of_mul hs0)
  have hsum : Summable (fun t : ℕ => γ ^ t * ∑ s0, ρ s0 * (npgM π P ^ t) s0 s) := by
    refine Summable.of_norm_bounded
      ((summable_geometric_of_lt_one hγ0 hγ1).mul_right (∑ s0, |ρ s0|)) ?_
    intro t
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hγ0 t)]
    refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg hγ0 t)
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun x _ => ?_)
    rw [abs_mul, abs_of_nonneg (npg_pow_nonneg hP hπ t x s)]
    exact mul_le_of_le_one_right (abs_nonneg _) (npg_pow_le_one hP hπ t x s)
  have hnn : ∀ t : ℕ, 0 ≤ γ ^ t * ∑ s0, ρ s0 * (npgM π P ^ t) s0 s := fun t =>
    mul_nonneg (pow_nonneg hγ0 t) (Finset.sum_nonneg fun x _ =>
      mul_nonneg (hρ0 x) (npg_pow_nonneg hP hπ t x s))
  have hpt : 0 < γ ^ t * ∑ s0, ρ s0 * (npgM π P ^ t) s0 s := by
    refine mul_pos hγt (lt_of_lt_of_le (mul_pos hρs hMs) ?_)
    exact Finset.single_le_sum (f := fun x => ρ x * (npgM π P ^ t) x s)
      (fun x _ => mul_nonneg (hρ0 x) (npg_pow_nonneg hP hπ t x s)) (Finset.mem_univ s0)
  exact mul_pos (by linarith) (hsum.tsum_pos hnn t hpt)

lemma npg_fisherOp_apply (P : S → A → S → ℝ) (γ : ℝ) (ρ : S → ℝ) (θ w : EuclideanSpace ℝ (S × A))
    (i : S × A) : fisherOp P γ ρ θ w i = ∑ j, fisher P γ ρ θ i j * w j := by
  rfl

lemma npg_score_dot [Nonempty A] (θ w : EuclideanSpace ℝ (S × A)) (s : S) (a : A) :
    ∑ j, scoreVec θ s a j * w j = w (s, a) - ∑ b, softmaxPolicy θ s b * w (s, b) := by
  simp only [npg_score_eq, Fintype.sum_prod_type]
  rw [Finset.sum_eq_single s (fun x _ hx => by simp [hx]) (by simp)]
  simp [sub_mul, Finset.sum_sub_distrib, ite_mul]

lemma npg_score_contract [Nonempty A] (θ : EuclideanSpace ℝ (S × A)) (d : S → ℝ) (z : S → A → ℝ)
    (i : S × A) :
    ∑ s, d s * ∑ a, softmaxPolicy θ s a * scoreVec θ s a i * z s a =
      d i.1 * (softmaxPolicy θ i.1 i.2 * z i.1 i.2 -
        softmaxPolicy θ i.1 i.2 * ∑ a, softmaxPolicy θ i.1 a * z i.1 a) := by
  simp only [npg_score_eq]
  rw [Finset.sum_eq_single i.1 (fun x _ hx => by simp [Ne.symm hx]) (by simp)]
  simp only [if_true]
  congr 1
  simp only [mul_sub, sub_mul, Finset.sum_sub_distrib, mul_ite, mul_one, mul_zero, ite_mul,
    zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  congr 1
  rw [Finset.mul_sum]; congr 1; ext x; ring

lemma npg_fisher_apply [Nonempty A] (P : S → A → S → ℝ) (γ : ℝ) (ρ : S → ℝ)
    (θ w : EuclideanSpace ℝ (S × A)) (i : S × A) :
    fisherOp P γ ρ θ w i = ∑ s, PolicyGradTheory.ProjGA.visitation (softmaxPolicy θ) P γ ρ s *
      ∑ a, softmaxPolicy θ s a * scoreVec θ s a i *
        (w (s, a) - ∑ b, softmaxPolicy θ s b * w (s, b)) := by
  rw [npg_fisherOp_apply]
  simp only [fisher, ← npg_score_dot θ w, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]; congr 1; ext s
  rw [Finset.sum_comm]; congr 1; ext a
  congr 1; ext j; ring

lemma npg_fisher_quad [Nonempty A] (P : S → A → S → ℝ) (γ : ℝ) (ρ : S → ℝ)
    (θ w : EuclideanSpace ℝ (S × A)) :
    ∑ i, w i * fisherOp P γ ρ θ w i = ∑ s, PolicyGradTheory.ProjGA.visitation (softmaxPolicy θ) P γ ρ s *
      ∑ a, softmaxPolicy θ s a * (w (s, a) - ∑ b, softmaxPolicy θ s b * w (s, b)) ^ 2 := by
  simp only [npg_fisher_apply, Finset.mul_sum]
  rw [Finset.sum_comm]; congr 1; ext s
  rw [Finset.sum_comm]; congr 1; ext a
  rw [← npg_score_dot θ w s a]
  have : ∀ x, w x * (PolicyGradTheory.ProjGA.visitation (softmaxPolicy θ) P γ ρ s *
      (softmaxPolicy θ s a * scoreVec θ s a x * ∑ j, scoreVec θ s a j * w j)) =
      (PolicyGradTheory.ProjGA.visitation (softmaxPolicy θ) P γ ρ s * softmaxPolicy θ s a *
        ∑ j, scoreVec θ s a j * w j) * (scoreVec θ s a x * w x) := by intro x; ring
  simp_rw [this]
  rw [← Finset.mul_sum]; ring

lemma npg_aux (X E K Ssum Z : ℝ) (hK : K ≠ 0) (hS : Ssum ≠ 0) (hZ : Z ≠ 0) :
    X * E * K / (Ssum * K) = X / Z * E / (Ssum / Z) := by
  field_simp

/-- Lemma 5.1, core -/
theorem npg_spi_core [Nonempty A] (P : S → A → S → ℝ) (r : S → A → ℝ) (γ : ℝ)
    (hM : PolicyGradTheory.ProjGA.IsFiniteMDP P r γ)
    (ρ : S → ℝ) (hρ : PolicyGradTheory.ProjGA.IsDist ρ) (hreach : AllReachable P γ ρ)
    (η : ℝ) (θ : ℕ → EuclideanSpace ℝ (S × A)) (hrun : IsNPGRun P r γ ρ η θ) :
    ∀ (t : ℕ) (s : S) (a : A),
      softmaxPolicy (θ (t + 1)) s a =
        softmaxPolicy (θ t) s a *
          Real.exp (η * PolicyGradTheory.ProjGA.advantage (softmaxPolicy (θ t)) P r γ s a / (1 - γ)) /
          npgNormalizer P r γ η (θ t) s := by
  intro t s a
  obtain ⟨B, hB, hθ⟩ := hrun t
  have hM' := hM
  obtain ⟨hP, hr, hγ0, hγ1⟩ := hM'
  set ϑ := θ t with hϑ
  set π := softmaxPolicy ϑ with hπdef
  have hπ : IsPolicy π := npg_sm_policy ϑ
  have hpos : ∀ s a, 0 < π s a := fun s a => npg_sm_pos ϑ s a
  set Adv := PolicyGradTheory.ProjGA.advantage π P r γ with hAdv
  set d := PolicyGradTheory.ProjGA.visitation π P γ ρ with hd
  have hdpos : ∀ s, 0 < d s := by
    intro s
    obtain ⟨π', hπ', h'⟩ := hreach s
    exact npg_vis_pos_of hP hπ hpos hγ0 hγ1 ρ hρ.1 s h'
  have hAsum : ∀ s, ∑ a, π s a * Adv s a = 0 := fun s => npg_adv_sum_self hP hπ hr hγ0 hγ1 s
  have hg : (1 - γ) ≠ 0 := by linarith
  set y := valueGrad P r γ ρ ϑ with hy
  set w0 : EuclideanSpace ℝ (S × A) := WithLp.toLp 2 (fun i : S × A => Adv i.1 i.2 / (1 - γ))
    with hw0
  have hw0a : ∀ i, w0 i = Adv i.1 i.2 / (1 - γ) := fun i => rfl
  have hFw0 : fisherOp P γ ρ ϑ w0 = y := by
    ext i
    rw [hy, npg_valueGrad_eq hM ρ ϑ, npg_fisher_apply]
    simp only [hw0a, PiLp.toLp_apply]
    have : ∀ s, ∑ b, π s b * (Adv s b / (1 - γ)) = 0 := by
      intro s; simp_rw [← mul_div_assoc]; rw [← Finset.sum_div, hAsum, zero_div]
    rw [← hπdef]
    simp_rw [this, sub_zero]
    rw [npg_score_contract ϑ d (fun s a => Adv s a / (1 - γ)) i]
    simp only [← hπdef, this]
    simp only [hd, hAdv, mul_zero, sub_zero]
    field_simp
  have hFBy : fisherOp P γ ρ ϑ (B y) = y := by
    have h1 := (hB y).1 w0
    rw [hFw0, sub_self, norm_zero] at h1
    exact sub_eq_zero.mp (norm_le_zero_iff.mp h1)
  set u := B y - w0 with hu
  have hFu : fisherOp P γ ρ ϑ u = 0 := by rw [hu, map_sub, hFBy, hFw0, sub_self]
  have hquad := npg_fisher_quad P γ ρ ϑ u
  rw [hFu] at hquad
  simp only [PiLp.zero_apply, mul_zero, Finset.sum_const_zero] at hquad
  have hu0 : ∀ s a, u (s, a) = ∑ b, π s b * u (s, b) := by
    intro s a
    have hnn : ∀ s ∈ Finset.univ, 0 ≤ d s *
        ∑ a, π s a * (u (s, a) - ∑ b, π s b * u (s, b)) ^ 2 := fun s _ =>
      mul_nonneg (hdpos s).le (Finset.sum_nonneg fun a _ => mul_nonneg (hpos s a).le (sq_nonneg _))
    have h1 := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hquad.symm s (Finset.mem_univ s)
    rcases mul_eq_zero.mp h1 with h1 | h1
    · exact absurd h1 (hdpos s).ne'
    have h2 := (Finset.sum_eq_zero_iff_of_nonneg (fun a _ =>
      mul_nonneg (hpos s a).le (sq_nonneg (u (s, a) - ∑ b, π s b * u (s, b))))).mp h1 a
      (Finset.mem_univ a)
    rcases mul_eq_zero.mp h2 with h2 | h2
    · exact absurd h2 (hpos s a).ne'
    have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h2
    linarith
  set c : S → ℝ := fun s => ∑ b, π s b * u (s, b) with hc
  have hθ1 : ∀ b, θ (t + 1) (s, b) = ϑ (s, b) + η * (Adv s b / (1 - γ)) + η * c s := by
    intro b
    have e1 : θ (t + 1) (s, b) = ϑ (s, b) + η * B y (s, b) := by
      rw [hθ]; simp
    have e2 : B y (s, b) = w0 (s, b) + u (s, b) := by rw [hu]; simp
    rw [e1, e2, hw0a, hu0 s b]; ring
  simp only [softmaxPolicy, npgNormalizer, hθ1, Real.exp_add]
  rw [← hπdef, ← hAdv]
  simp only [softmaxPolicy, hπdef, ← hϑ]
  have hZ := npg_Z_pos ϑ s
  have hsum : ∑ x, Real.exp (ϑ (s, x)) * Real.exp (η * (Adv s x / (1 - γ))) * Real.exp (η * c s) =
      (∑ x, Real.exp (ϑ (s, x)) * Real.exp (η * (Adv s x / (1 - γ)))) * Real.exp (η * c s) := by
    rw [Finset.sum_mul]
  simp_rw [mul_div_assoc η]
  rw [hsum]
  have hsum2 : ∑ x, Real.exp (ϑ (s, x)) / (∑ b, Real.exp (ϑ (s, b))) *
      Real.exp (η * (Adv s x / (1 - γ))) =
      (∑ x, Real.exp (ϑ (s, x)) * Real.exp (η * (Adv s x / (1 - γ)))) /
        ∑ b, Real.exp (ϑ (s, b)) := by
    rw [Finset.sum_div]; congr 1; ext x; ring
  rw [hsum2]
  have hpos2 : 0 < ∑ x, Real.exp (ϑ (s, x)) * Real.exp (η * (Adv s x / (1 - γ))) :=
    Finset.sum_pos (fun x _ => mul_pos (Real.exp_pos _) (Real.exp_pos _)) Finset.univ_nonempty
  exact npg_aux _ _ _ _ _ (Real.exp_pos _).ne' hpos2.ne' hZ.ne'

end Fisher

section Imp
variable {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A] [DecidableEq A]

lemma npg_logZ_le [Nonempty A] (p q x : A → ℝ) (hp : ∀ a, 0 < p a)
    (hq : ∀ a, q a = p a * Real.exp (x a) / ∑ b, p b * Real.exp (x b)) (hpsum : ∑ a, p a = 1) :
    Real.log (∑ b, p b * Real.exp (x b)) ≤ ∑ a, q a * x a := by
  set Z := ∑ b, p b * Real.exp (x b) with hZdef
  have hZ : 0 < Z := Finset.sum_pos (fun b _ => mul_pos (hp b) (Real.exp_pos _))
    Finset.univ_nonempty
  have hqsum : ∑ a, q a = 1 := by
    simp_rw [hq, ← Finset.sum_div]; exact div_self hZ.ne'
  have hq0 : ∀ a, 0 ≤ q a := by
    intro a; rw [hq a]; exact div_nonneg (mul_nonneg (hp a).le (Real.exp_pos _).le) hZ.le
  have key : ∀ a, q a * (Real.log Z - x a) ≤ q a * (Z * Real.exp (-x a) - 1) := by
    intro a; apply mul_le_mul_of_nonneg_left _ (hq0 a)
    have := Real.log_le_sub_one_of_pos (mul_pos hZ (Real.exp_pos (-x a)))
    rwa [Real.log_mul hZ.ne' (Real.exp_pos _).ne', Real.log_exp, ← sub_eq_add_neg] at this
  have hsum : ∑ a, q a * (Z * Real.exp (-x a) - 1) = 0 := by
    have : ∀ a, q a * (Z * Real.exp (-x a) - 1) = p a - q a := by
      intro a
      have e : Real.exp (x a) * Real.exp (-x a) = 1 := by
        rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
      rw [hq a]
      field_simp
      linear_combination (p a * Z) * e
    simp_rw [this, Finset.sum_sub_distrib, hpsum, hqsum, sub_self]
  have := Finset.sum_le_sum (fun a (_ : a ∈ Finset.univ) => key a)
  rw [hsum] at this
  simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hqsum, one_mul] at this
  linarith

lemma npg_logZ_nonneg (p x : A → ℝ) (hp : ∀ a, 0 ≤ p a) (hpsum : ∑ a, p a = 1)
    (hx : ∑ a, p a * x a = 0) : 0 ≤ Real.log (∑ b, p b * Real.exp (x b)) := by
  apply Real.log_nonneg
  calc (1 : ℝ) = ∑ a, p a * (x a + 1) := by
        simp [mul_add, Finset.sum_add_distrib, hx, hpsum]
    _ ≤ ∑ b, p b * Real.exp (x b) :=
        Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_left (Real.add_one_le_exp _) (hp a)

lemma npg_vis_summable {P : S → A → S → ℝ} (hP : IsTransitionKernel P) {π : S → A → ℝ}
    (hπ : IsPolicy π) {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (ρ : S → ℝ) (s : S) :
    Summable (fun t : ℕ => γ ^ t * ∑ s0, ρ s0 * (npgM π P ^ t) s0 s) := by
  refine Summable.of_norm_bounded
    ((summable_geometric_of_lt_one hγ0 hγ1).mul_right (∑ s0, |ρ s0|)) ?_
  intro t
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hγ0 t)]
  refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg hγ0 t)
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun x _ => ?_)
  rw [abs_mul, abs_of_nonneg (npg_pow_nonneg hP hπ t x s)]
  exact mul_le_of_le_one_right (abs_nonneg _) (npg_pow_le_one hP hπ t x s)

lemma npg_vis_ge {P : S → A → S → ℝ} (hP : IsTransitionKernel P) {π : S → A → ℝ}
    (hπ : IsPolicy π) {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (ρ : S → ℝ) (hρ0 : ∀ x, 0 ≤ ρ x)
    (s : S) : (1 - γ) * ρ s ≤ PolicyGradTheory.ProjGA.visitation π P γ ρ s := by
  unfold PolicyGradTheory.ProjGA.visitation
  simp only [npg_occ_eq_pow]
  apply mul_le_mul_of_nonneg_left _ (by linarith)
  have := (npg_vis_summable hP hπ hγ0 hγ1 ρ s).le_tsum 0 (fun j _ =>
    mul_nonneg (pow_nonneg hγ0 j) (Finset.sum_nonneg fun x _ =>
      mul_nonneg (hρ0 x) (npg_pow_nonneg hP hπ j x s)))
  simpa [Matrix.one_apply] using this

lemma npg_value_nonneg {P : S → A → S → ℝ} (hP : IsTransitionKernel P) {π : S → A → ℝ}
    (hπ : IsPolicy π) {r : S → A → ℝ} (hr : ∀ s a, 0 ≤ r s a ∧ r s a ≤ 1) {γ : ℝ}
    (hγ0 : 0 ≤ γ) (s : S) : 0 ≤ PolicyValue π P r γ s := by
  rw [npg_value_eq]
  exact tsum_nonneg fun t => mul_nonneg (pow_nonneg hγ0 t) (Finset.sum_nonneg fun x _ =>
    mul_nonneg (npg_pow_nonneg hP hπ t s x)
      (Finset.sum_nonneg fun a _ => mul_nonneg ((hπ x).1 a) (hr x a).1))

/-- Lemma 5.2, core -/
theorem npg_ilb_core [Nonempty A] (P : S → A → S → ℝ) (r : S → A → ℝ) (γ : ℝ)
    (hM : PolicyGradTheory.ProjGA.IsFiniteMDP P r γ)
    (ρ : S → ℝ) (hρ : PolicyGradTheory.ProjGA.IsDist ρ) (hreach : AllReachable P γ ρ)
    (η : ℝ) (hη : 0 < η) (θ : ℕ → EuclideanSpace ℝ (S × A)) (hrun : IsNPGRun P r γ ρ η θ)
    (μ : S → ℝ) (hμ : PolicyGradTheory.ProjGA.IsDist μ) :
    ∀ t : ℕ,
      (1 - γ) / η * ∑ s, μ s * Real.log (npgNormalizer P r γ η (θ t) s) ≤
          PolicyGradTheory.ProjGA.valueAt (softmaxPolicy (θ (t + 1))) P r γ μ -
            PolicyGradTheory.ProjGA.valueAt (softmaxPolicy (θ t)) P r γ μ ∧
        0 ≤ (1 - γ) / η * ∑ s, μ s * Real.log (npgNormalizer P r γ η (θ t) s) := by
  intro t
  have hspi := npg_spi_core P r γ hM ρ hρ hreach η θ hrun t
  obtain ⟨hP, hr, hγ0, hγ1⟩ := hM
  have hg : 0 < 1 - γ := by linarith
  have hπ0 := npg_sm_policy (θ t)
  have hπ1 := npg_sm_policy (θ (t + 1))
  have hAsum := npg_adv_sum_self hP hπ0 hr hγ0 hγ1
  have hZnn : ∀ s, 0 ≤ Real.log (npgNormalizer P r γ η (θ t) s) := by
    intro s
    unfold npgNormalizer
    apply npg_logZ_nonneg _ _ (fun a => (npg_sm_pos _ s a).le) (npg_sm_sum _ s)
    have : ∀ a, softmaxPolicy (θ t) s a *
        (η * PolicyGradTheory.ProjGA.advantage (softmaxPolicy (θ t)) P r γ s a / (1 - γ)) =
        η / (1 - γ) * (softmaxPolicy (θ t) s a *
          PolicyGradTheory.ProjGA.advantage (softmaxPolicy (θ t)) P r γ s a) := by
      intro a; ring
    simp_rw [this]; rw [← Finset.mul_sum, hAsum s, mul_zero]
  have hstep : ∀ s, (1 - γ) / η * Real.log (npgNormalizer P r γ η (θ t) s) ≤
      ∑ a, softmaxPolicy (θ (t + 1)) s a *
        PolicyGradTheory.ProjGA.advantage (softmaxPolicy (θ t)) P r γ s a := by
    intro s
    have h1 := npg_logZ_le (softmaxPolicy (θ t) s) (softmaxPolicy (θ (t + 1)) s)
      (fun a => η * PolicyGradTheory.ProjGA.advantage (softmaxPolicy (θ t)) P r γ s a / (1 - γ))
      (fun a => npg_sm_pos _ s a) (fun a => hspi s a) (npg_sm_sum _ s)
    have e : ∑ a, softmaxPolicy (θ (t + 1)) s a *
        (η * PolicyGradTheory.ProjGA.advantage (softmaxPolicy (θ t)) P r γ s a / (1 - γ)) =
        η / (1 - γ) * ∑ a, softmaxPolicy (θ (t + 1)) s a *
          PolicyGradTheory.ProjGA.advantage (softmaxPolicy (θ t)) P r γ s a := by
      rw [Finset.mul_sum]; congr 1; ext a; ring
    rw [e] at h1
    unfold npgNormalizer
    calc (1 - γ) / η * Real.log _ ≤ (1 - γ) / η * (η / (1 - γ) * ∑ a, softmaxPolicy (θ (t + 1)) s a *
          PolicyGradTheory.ProjGA.advantage (softmaxPolicy (θ t)) P r γ s a) :=
          mul_le_mul_of_nonneg_left h1 (div_nonneg hg.le hη.le)
      _ = _ := by field_simp
  refine ⟨?_, mul_nonneg (div_nonneg hg.le hη.le)
    (Finset.sum_nonneg fun s _ => mul_nonneg (hμ.1 s) (hZnn s))⟩
  rw [npg_pdl hP hπ1 hπ0 hr hγ0 hγ1 μ, Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro s _
  have hv := npg_vis_ge hP hπ1 hγ0 hγ1 μ hμ.1 s
  have hz := hZnn s
  have hst := hstep s
  have hm := hμ.1 s
  have h1 : (1 - γ) / η * (μ s * Real.log (npgNormalizer P r γ η (θ t) s)) =
      1 / (1 - γ) * (((1 - γ) * μ s) * ((1 - γ) / η * Real.log (npgNormalizer P r γ η (θ t) s))) := by
    field_simp
  rw [h1]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  calc ((1 - γ) * μ s) * ((1 - γ) / η * Real.log (npgNormalizer P r γ η (θ t) s))
      ≤ PolicyGradTheory.ProjGA.visitation (softmaxPolicy (θ (t + 1))) P γ μ s *
          ((1 - γ) / η * Real.log (npgNormalizer P r γ η (θ t) s)) :=
        mul_le_mul_of_nonneg_right hv (mul_nonneg (div_nonneg hg.le hη.le) hz)
    _ ≤ _ := mul_le_mul_of_nonneg_left hst (le_trans (mul_nonneg hg.le hm) hv)

/-- monotonicity, core -/
theorem npg_mono_core [Nonempty A] (P : S → A → S → ℝ) (r : S → A → ℝ) (γ : ℝ)
    (hM : PolicyGradTheory.ProjGA.IsFiniteMDP P r γ)
    (ρ : S → ℝ) (hρ : PolicyGradTheory.ProjGA.IsDist ρ) (hreach : AllReachable P γ ρ)
    (η : ℝ) (hη : 0 < η) (θ : ℕ → EuclideanSpace ℝ (S × A)) (hrun : IsNPGRun P r γ ρ η θ) :
    ∀ (t : ℕ) (s : S),
      PolicyValue (softmaxPolicy (θ t)) P r γ s ≤
        PolicyValue (softmaxPolicy (θ (t + 1))) P r γ s := by
  intro t s
  have hδ : PolicyGradTheory.ProjGA.IsDist (fun x : S => if x = s then (1 : ℝ) else 0) :=
    ⟨fun x => by dsimp only; split_ifs <;> norm_num, by simp⟩
  have h := npg_ilb_core P r γ hM ρ hρ hreach η hη θ hrun _ hδ t
  have := h.2.trans h.1
  simpa [PolicyGradTheory.ProjGA.valueAt] using this

end Imp

end PolicyGradTheory.NPG

open PolicyGradTheory.NPG


theorem solution {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A] [DecidableEq A]
    (P : S → A → S → ℝ) (r : S → A → ℝ) (γ : ℝ) (hM : PolicyGradTheory.ProjGA.IsFiniteMDP P r γ)
    [Nonempty A] (ρ : S → ℝ) (hρ : PolicyGradTheory.ProjGA.IsDist ρ) (hreach : AllReachable P γ ρ)
    (η : ℝ) (hη : 0 < η) (θ : ℕ → EuclideanSpace ℝ (S × A)) (hrun : IsNPGRun P r γ ρ η θ) :
    ∀ (t : ℕ) (s : S),
      PolicyValue (softmaxPolicy (θ t)) P r γ s ≤
        PolicyValue (softmaxPolicy (θ (t + 1))) P r γ s := by
  exact npg_mono_core P r γ hM ρ hρ hreach η hη θ hrun
