import Mathlib
import Definitions.Def_HighDimProb_Isoperimetry_UniformProjection

open MeasureTheory ProbabilityTheory

namespace HighDimProb.Isoperimetry.RPAux

/-! Vershynin, Lemma 5.3.2(b) (random projection, concentration), with `c = 1/144`.

* (Q1) Chernoff bounds for `Σ_{i∈S} gᵢ²` with i.i.d. standard normal `gᵢ`.
* (Q2) For a fixed orthogonal projection `Q` of rank `m`, `(‖Q g‖, ‖g‖)` under the standard
  Gaussian has the law of `(√Σ_{i∈S} xᵢ², √Σ_i xᵢ²)` with `|S| = m` (eigenbasis of `Q`), and
  the ratio concentrates around `√(m/n)` with failure probability `≤ 4 exp(-ε² m / 72)`.
* (Q3) By rotation invariance of the law of `P`, `‖P z‖` has the same law for every unit `z`;
  averaging `z = g / ‖g‖` over a Gaussian `g` and swapping integrals reduces to (Q2). -/

/-- One-dimensional Gaussian integral: `E exp(λ g²) = √(1+t)` for `λ = t/(2(1+t))`. -/
theorem Q1_upper_integral_exp_sq {t : ℝ} (ht : 0 ≤ t) :
    ∫ y, Real.exp (t / (2 * (1 + t)) * y ^ 2) ∂(gaussianReal 0 1) = Real.sqrt (1 + t) := by
  have h1t : 0 < 1 + t := by linarith
  rw [integral_gaussianReal_eq_integral_smul (by norm_num)]
  simp only [gaussianPDFReal, smul_eq_mul, NNReal.coe_one, mul_one, sub_zero]
  have key : ∀ y : ℝ, (√(2 * Real.pi))⁻¹ * Real.exp (-y ^ 2 / 2) *
      Real.exp (t / (2 * (1 + t)) * y ^ 2)
      = (√(2 * Real.pi))⁻¹ * Real.exp (-(1 / (2 * (1 + t))) * y ^ 2) := by
    intro y
    rw [mul_assoc, ← Real.exp_add]
    congr 2
    field_simp
    ring
  simp_rw [key]
  rw [integral_const_mul, integral_gaussian]
  rw [show Real.pi / (1 / (2 * (1 + t))) = (2 * Real.pi) * (1 + t) by field_simp]
  rw [Real.sqrt_mul (show (0:ℝ) ≤ 2 * Real.pi by positivity) (1 + t)]
  have : 0 < √(2 * Real.pi) := Real.sqrt_pos.mpr (by positivity)
  field_simp

/-- Integrability and value of the mgf of `Σ_{i∈S} xᵢ²` at `λ = t/(2(1+t))`. -/
theorem Q1_upper_mgf {ι : Type} [Fintype ι] (S : Finset ι) {t : ℝ} (ht : 0 ≤ t) :
    (Integrable (fun x : ι → ℝ => Real.exp (t / (2 * (1 + t)) * ∑ i ∈ S, x i ^ 2))
      (Measure.pi (fun _ : ι => gaussianReal 0 1))) ∧
    mgf (fun x : ι → ℝ => ∑ i ∈ S, x i ^ 2) (Measure.pi (fun _ : ι => gaussianReal 0 1))
      (t / (2 * (1 + t))) = Real.sqrt (1 + t) ^ S.card := by
  classical
  set l := t / (2 * (1 + t)) with hl
  let f : ι → ℝ → ℝ := fun i y => if i ∈ S then Real.exp (l * y ^ 2) else 1
  have hprod : (fun x : ι → ℝ => Real.exp (l * ∑ i ∈ S, x i ^ 2)) =
      fun x => ∏ i, f i (x i) := by
    funext x
    simp only [f]
    rw [Fintype.prod_ite_mem, Finset.mul_sum, Real.exp_sum]
  have hint1 : Integrable (fun y => Real.exp (l * y ^ 2)) (gaussianReal 0 1) := by
    apply Integrable.of_integral_ne_zero
    rw [Q1_upper_integral_exp_sq ht]
    exact (Real.sqrt_pos.mpr (by linarith)).ne'
  have hf : ∀ i, Integrable (f i) (gaussianReal 0 1) := by
    intro i
    by_cases hi : i ∈ S
    · simp only [f, hi, if_true]; exact hint1
    · simp only [f, hi, if_false]; exact integrable_const _
  refine ⟨?_, ?_⟩
  · rw [hprod]; exact Integrable.fintype_prod hf
  · rw [mgf, hprod, integral_fintype_prod_eq_prod]
    have : ∀ i, ∫ y, f i y ∂(gaussianReal 0 1) = if i ∈ S then Real.sqrt (1 + t) else 1 := by
      intro i
      by_cases hi : i ∈ S
      · simp only [f, hi, if_true]; exact Q1_upper_integral_exp_sq ht
      · simp [f, hi]
    simp_rw [this]
    rw [Fintype.prod_ite_mem, Finset.prod_const]

/-- (Q1u) Chernoff upper tail for a chi-square sum over a finite set of coordinates. -/
theorem Q1_upper {ι : Type} [Fintype ι] (S : Finset ι) {t : ℝ} (ht : 0 ≤ t) :
    (Measure.pi (fun _ : ι => gaussianReal 0 1)).real
        {x | (S.card : ℝ) * (1 + t) ≤ ∑ i ∈ S, x i ^ 2}
      ≤ Real.exp (-((S.card : ℝ) * (t - Real.log (1 + t)) / 2)) := by
  have h1t : 0 < 1 + t := by linarith
  obtain ⟨hint, hmgf⟩ := Q1_upper_mgf S ht
  have hl : 0 ≤ t / (2 * (1 + t)) := by positivity
  refine (measure_ge_le_exp_mul_mgf ((S.card : ℝ) * (1 + t)) hl hint).trans (le_of_eq ?_)
  rw [hmgf, Real.sqrt_eq_rpow, Real.rpow_def_of_pos h1t, ← Real.exp_nat_mul, ← Real.exp_add]
  congr 1
  field_simp
  ring

/-- The Gaussian integral of `exp (-l y²)` against the standard normal law. -/
theorem Q1_lower_integral_1d (l : ℝ) :
    ∫ y, Real.exp (-l * y ^ 2) ∂(gaussianReal 0 1) =
      Real.sqrt (Real.pi / (1 / 2 + l)) / Real.sqrt (2 * Real.pi) := by
  rw [integral_gaussianReal_eq_integral_smul (by norm_num)]
  have h : ∀ x : ℝ, gaussianPDFReal 0 1 x • Real.exp (-l * x ^ 2) =
      (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(1 / 2 + l) * x ^ 2) := by
    intro x
    rw [gaussianPDFReal, smul_eq_mul, mul_assoc, ← Real.exp_add]
    simp only [NNReal.coe_one, mul_one]
    congr 2
    ring
  simp_rw [h]
  rw [integral_const_mul, integral_gaussian]
  ring

/-- `log (1 - t) ≤ -t - t²/2` for `0 ≤ t < 1`. -/
theorem Q1_lower_log_bound {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) :
    Real.log (1 - t) ≤ -t - t ^ 2 / 2 := by
  have habs : |t| < 1 := by rw [abs_of_nonneg ht0]; exact ht1
  have hs := Real.hasSum_pow_div_log_of_abs_lt_one habs
  have := sum_le_hasSum (Finset.range 2) (fun n _ => by positivity) hs
  simp [Finset.sum_range_succ] at this
  linarith

/-- The integral of `exp (-l Σ_{i∈S} xᵢ²)` factorizes over the coordinates. -/
theorem Q1_lower_integral_prod {ι : Type} [Fintype ι] (S : Finset ι) (l : ℝ) :
    ∫ x, Real.exp (-l * ∑ i ∈ S, x i ^ 2) ∂(Measure.pi (fun _ : ι => gaussianReal 0 1)) =
      (∫ y, Real.exp (-l * y ^ 2) ∂(gaussianReal 0 1)) ^ S.card := by
  classical
  set f : ι → ℝ → ℝ := fun i y => if i ∈ S then Real.exp (-l * y ^ 2) else 1 with hf
  have h : ∀ x : ι → ℝ, Real.exp (-l * ∑ i ∈ S, x i ^ 2) = ∏ i, f i (x i) := by
    intro x
    rw [hf, Finset.mul_sum, Real.exp_sum, Finset.prod_ite_mem, Finset.univ_inter]
  simp_rw [h]
  rw [integral_fintype_prod_eq_prod]
  have h2 : ∀ i, ∫ y, f i y ∂(gaussianReal 0 1) =
      if i ∈ S then ∫ y, Real.exp (-l * y ^ 2) ∂(gaussianReal 0 1) else 1 := by
    intro i
    by_cases hi : i ∈ S <;> simp [hf, hi]
  simp_rw [h2]
  rw [Finset.prod_ite_mem, Finset.univ_inter, Finset.prod_const]

/-- Integrability of `exp (-l Σ_{i∈S} xᵢ²)` for `l ≥ 0`. -/
theorem Q1_lower_integrable {ι : Type} [Fintype ι] (S : Finset ι) {l : ℝ} (hl : 0 ≤ l) :
    Integrable (fun x : ι → ℝ => Real.exp (-l * ∑ i ∈ S, x i ^ 2))
      (Measure.pi (fun _ : ι => gaussianReal 0 1)) := by
  refine Integrable.of_bound (by fun_prop : Measurable _).aestronglyMeasurable 1
    (ae_of_all _ fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_le_one_iff]
  have : 0 ≤ ∑ i ∈ S, x i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  nlinarith

/-- (Q1l) Chernoff lower tail for a chi-square sum over a finite set of coordinates. -/
theorem Q1_lower {ι : Type} [Fintype ι] (S : Finset ι) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) :
    (Measure.pi (fun _ : ι => gaussianReal 0 1)).real
        {x | ∑ i ∈ S, x i ^ 2 ≤ (S.card : ℝ) * (1 - t)}
      ≤ Real.exp (-((S.card : ℝ) * t ^ 2 / 4)) := by
  have h1t : 0 < 1 - t := by linarith
  set l : ℝ := t / (2 * (1 - t)) with hl
  have hl0 : 0 ≤ l := div_nonneg ht0 (by linarith)
  have hch := measure_le_le_exp_mul_mgf (μ := Measure.pi (fun _ : ι => gaussianReal 0 1))
    (X := fun x : ι → ℝ => ∑ i ∈ S, x i ^ 2) ((S.card : ℝ) * (1 - t)) (t := -l)
    (by linarith) (Q1_lower_integrable S hl0)
  refine hch.trans ?_
  rw [mgf, Q1_lower_integral_prod, Q1_lower_integral_1d]
  have hc : Real.sqrt (Real.pi / (1 / 2 + l)) / Real.sqrt (2 * Real.pi) = Real.sqrt (1 - t) := by
    have h2 : Real.pi / (1 / 2 + l) = (2 * Real.pi) * (1 - t) := by
      rw [hl]
      field_simp
      ring
    rw [h2, Real.sqrt_mul (by positivity),
      mul_div_cancel_left₀ _ (ne_of_gt (Real.sqrt_pos.2 (by positivity)))]
  have he : -(-l) * ((S.card : ℝ) * (1 - t)) = (S.card : ℝ) * (t / 2) := by
    rw [hl]
    field_simp
  have hs : Real.sqrt (1 - t) ≤ Real.exp (-t / 2 - t ^ 2 / 4) := by
    rw [show -t / 2 - t ^ 2 / 4 = (-t - t ^ 2 / 2) / 2 by ring, Real.exp_half]
    apply Real.sqrt_le_sqrt
    calc 1 - t = Real.exp (Real.log (1 - t)) := (Real.exp_log h1t).symm
      _ ≤ Real.exp (-t - t ^ 2 / 2) := Real.exp_le_exp.2 (Q1_lower_log_bound ht0 ht1)
  rw [hc, he]
  calc Real.exp ((S.card : ℝ) * (t / 2)) * Real.sqrt (1 - t) ^ S.card
      ≤ Real.exp ((S.card : ℝ) * (t / 2)) * Real.exp (-t / 2 - t ^ 2 / 4) ^ S.card := by
        gcongr
    _ = Real.exp (-((S.card : ℝ) * t ^ 2 / 4)) := by
        rw [← Real.exp_nat_mul, ← Real.exp_add]
        congr 1
        ring

theorem Q2_coord_sqrt_lower {c a T X : ℝ} (ha : 0 ≤ a) (hT : 0 ≤ T) (h : c ^ 2 * a * T ≤ X) :
    c * Real.sqrt a * Real.sqrt T ≤ Real.sqrt X := by
  apply Real.le_sqrt_of_sq_le
  rw [mul_pow, mul_pow, Real.sq_sqrt ha, Real.sq_sqrt hT]
  exact h

theorem Q2_coord_sqrt_upper {c a T X : ℝ} (hc : 0 ≤ c) (ha : 0 ≤ a) (hT : 0 ≤ T)
    (h : X ≤ c ^ 2 * a * T) :
    Real.sqrt X ≤ c * Real.sqrt a * Real.sqrt T := by
  rw [Real.sqrt_le_iff]
  refine ⟨by positivity, ?_⟩
  rw [mul_pow, mul_pow, Real.sq_sqrt ha, Real.sq_sqrt hT]
  exact h

theorem Q2_coord_neg_lower {c a T X : ℝ} (hc : c ≤ 0) :
    c * Real.sqrt a * Real.sqrt T ≤ Real.sqrt X := by
  have h1 : c * Real.sqrt a ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hc (Real.sqrt_nonneg _)
  have h2 : c * Real.sqrt a * Real.sqrt T ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg h1 (Real.sqrt_nonneg _)
  exact h2.trans (Real.sqrt_nonneg _)

theorem Q2_coord_log_bound {t c : ℝ} (ht : 0 ≤ t) (htc : 0 ≤ t - c) (h2 : 2 * c ≤ (t - c) ^ 2) :
    c ≤ t - Real.log (1 + t) := by
  have h1 : 0 < 1 + t := by linarith
  have : Real.log (1 + t) ≤ t - c := by
    rw [Real.log_le_iff_le_exp h1]
    have := Real.quadratic_le_exp_of_nonneg htc
    nlinarith
  linarith

theorem Q2_coord_four {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    {s A B C D : Set α} {b : ℝ} (h : s ⊆ A ∪ B ∪ C ∪ D) (hA : μ.real A ≤ b)
    (hB : μ.real B ≤ b) (hC : μ.real C ≤ b) (hD : μ.real D ≤ b) : μ.real s ≤ 4 * b := by
  have h0 := measureReal_mono (μ := μ) h
  have h1 := measureReal_union_le (μ := μ) (A ∪ B ∪ C) D
  have h2 := measureReal_union_le (μ := μ) (A ∪ B) C
  have h3 := measureReal_union_le (μ := μ) A B
  linarith

theorem Q2_coord_pw_small {m n : ℕ} (hn : 0 < (n : ℝ)) {ε X T : ℝ} (hε0 : 0 < ε)
    (hε1 : ε ≤ 1) (hT0 : 0 ≤ T) (h1 : X < m * (1 + ε / 3)) (h2 : m * (1 - ε / 3) < X)
    (h3 : T < n * (1 + ε / 3)) (h4 : n * (1 - ε / 3) < T) :
    (1 - ε) * Real.sqrt ((m : ℝ) / n) * Real.sqrt T ≤ Real.sqrt X ∧
      Real.sqrt X ≤ (1 + ε) * Real.sqrt ((m : ℝ) / n) * Real.sqrt T := by
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have ha : 0 ≤ (m : ℝ) / n := by positivity
  have hu1 : (m : ℝ) * (1 - ε / 3) ≤ (m : ℝ) / n * T := by
    calc (m : ℝ) * (1 - ε / 3) = (m : ℝ) / n * (n * (1 - ε / 3)) := by
          field_simp
      _ ≤ (m : ℝ) / n * T := mul_le_mul_of_nonneg_left h4.le ha
  have hu2 : (m : ℝ) / n * T ≤ (m : ℝ) * (1 + ε / 3) := by
    calc (m : ℝ) / n * T ≤ (m : ℝ) / n * (n * (1 + ε / 3)) :=
          mul_le_mul_of_nonneg_left h3.le ha
      _ = (m : ℝ) * (1 + ε / 3) := by field_simp
  constructor
  · apply Q2_coord_sqrt_lower ha hT0
    have key : (1 - ε) ^ 2 * (1 + ε / 3) ≤ 1 - ε / 3 := by
      have : 0 ≤ 4 - ε - ε ^ 2 := by nlinarith
      nlinarith [mul_nonneg hε0.le this]
    calc (1 - ε) ^ 2 * ((m : ℝ) / n) * T = (1 - ε) ^ 2 * ((m : ℝ) / n * T) := by ring
      _ ≤ (1 - ε) ^ 2 * ((m : ℝ) * (1 + ε / 3)) :=
          mul_le_mul_of_nonneg_left hu2 (sq_nonneg _)
      _ = (m : ℝ) * ((1 - ε) ^ 2 * (1 + ε / 3)) := by ring
      _ ≤ (m : ℝ) * (1 - ε / 3) := mul_le_mul_of_nonneg_left key hm0
      _ ≤ X := h2.le
  · apply Q2_coord_sqrt_upper (by linarith) ha hT0
    have key : 1 + ε / 3 ≤ (1 + ε) ^ 2 * (1 - ε / 3) := by
      have : 0 ≤ 4 + ε - ε ^ 2 := by nlinarith
      nlinarith [mul_nonneg hε0.le this]
    calc X ≤ (m : ℝ) * (1 + ε / 3) := h1.le
      _ ≤ (m : ℝ) * ((1 + ε) ^ 2 * (1 - ε / 3)) := mul_le_mul_of_nonneg_left key hm0
      _ = (1 + ε) ^ 2 * ((m : ℝ) * (1 - ε / 3)) := by ring
      _ ≤ (1 + ε) ^ 2 * ((m : ℝ) / n * T) := mul_le_mul_of_nonneg_left hu1 (sq_nonneg _)
      _ = (1 + ε) ^ 2 * ((m : ℝ) / n) * T := by ring

theorem Q2_coord_pw_big1 {m n : ℕ} (hn : 0 < (n : ℝ)) {ε X T : ℝ} (hε : 1 < ε)
    (hT0 : 0 ≤ T) (hXT : X ≤ T) (hmn : (n : ℝ) ≤ (1 + ε) ^ 2 * m) :
    (1 - ε) * Real.sqrt ((m : ℝ) / n) * Real.sqrt T ≤ Real.sqrt X ∧
      Real.sqrt X ≤ (1 + ε) * Real.sqrt ((m : ℝ) / n) * Real.sqrt T := by
  have ha : 0 ≤ (m : ℝ) / n := by positivity
  refine ⟨Q2_coord_neg_lower (by linarith), ?_⟩
  apply Q2_coord_sqrt_upper (by linarith) ha hT0
  have h1 : 1 ≤ (1 + ε) ^ 2 * ((m : ℝ) / n) := by
    rw [← mul_div_assoc, le_div_iff₀ hn]
    linarith
  nlinarith

theorem Q2_coord_pw_big2 {m n : ℕ} (hn : 0 < (n : ℝ)) {ε X T : ℝ} (hε : 1 < ε)
    (hT0 : 0 ≤ T) (h1 : X < m * (1 + ((1 + ε) ^ 2 / 2 - 1))) (h4 : n * (1 - 1 / 2) < T) :
    (1 - ε) * Real.sqrt ((m : ℝ) / n) * Real.sqrt T ≤ Real.sqrt X ∧
      Real.sqrt X ≤ (1 + ε) * Real.sqrt ((m : ℝ) / n) * Real.sqrt T := by
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have ha : 0 ≤ (m : ℝ) / n := by positivity
  refine ⟨Q2_coord_neg_lower (by linarith), ?_⟩
  apply Q2_coord_sqrt_upper (by linarith) ha hT0
  have hu1 : (m : ℝ) * (1 - 1 / 2) ≤ (m : ℝ) / n * T := by
    calc (m : ℝ) * (1 - 1 / 2) = (m : ℝ) / n * (n * (1 - 1 / 2)) := by
          field_simp
      _ ≤ (m : ℝ) / n * T := mul_le_mul_of_nonneg_left h4.le ha
  calc X ≤ (m : ℝ) * (1 + ((1 + ε) ^ 2 / 2 - 1)) := h1.le
    _ = (1 + ε) ^ 2 * ((m : ℝ) * (1 - 1 / 2)) := by ring
    _ ≤ (1 + ε) ^ 2 * ((m : ℝ) / n * T) := mul_le_mul_of_nonneg_left hu1 (sq_nonneg _)
    _ = (1 + ε) ^ 2 * ((m : ℝ) / n) * T := by ring

/-- (Q2c) Concentration of the ratio `√(Σ_{i∈S} xᵢ²) / √(Σ_i xᵢ²)` around `√(m/n)`. -/
theorem Q2_coord {n : ℕ} (S : Finset (Fin n)) {m : ℕ} (hS : S.card = m) {ε : ℝ} (hε : 0 < ε) :
    (Measure.pi (fun _ : Fin n => gaussianReal 0 1)).real
      {x | ¬ ((1 - ε) * Real.sqrt ((m : ℝ) / n) * Real.sqrt (∑ i, x i ^ 2) ≤
                Real.sqrt (∑ i ∈ S, x i ^ 2) ∧
              Real.sqrt (∑ i ∈ S, x i ^ 2) ≤
                (1 + ε) * Real.sqrt ((m : ℝ) / n) * Real.sqrt (∑ i, x i ^ 2))}
      ≤ 4 * Real.exp (-(ε ^ 2 * m / 72)) := by
  classical
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    calc (Measure.pi (fun _ : Fin n => gaussianReal 0 1)).real _ ≤ 1 := measureReal_le_one
      _ ≤ 4 * Real.exp (-(ε ^ 2 * ((0 : ℕ) : ℝ) / 72)) := by
          simp only [Nat.cast_zero, mul_zero, zero_div, neg_zero, Real.exp_zero, mul_one]
          norm_num
  have hmn : m ≤ n := by
    have := S.card_le_univ
    rwa [Fintype.card_fin, hS] at this
  have hn : 0 < n := lt_of_lt_of_le hm hmn
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hmnR : (m : ℝ) ≤ n := by exact_mod_cast hmn
  have hUpS : ∀ t : ℝ, 0 ≤ t → ε ^ 2 * m / 36 ≤ m * (t - Real.log (1 + t)) →
      (Measure.pi (fun _ : Fin n => gaussianReal 0 1)).real
        {x | (m : ℝ) * (1 + t) ≤ ∑ i ∈ S, x i ^ 2} ≤ Real.exp (-(ε ^ 2 * m / 72)) := by
    intro t ht hlog
    have := Q1_upper S ht
    rw [hS] at this
    refine this.trans (Real.exp_le_exp.mpr ?_)
    linarith
  have hUpU : ∀ t : ℝ, 0 ≤ t → ε ^ 2 * m / 36 ≤ n * (t - Real.log (1 + t)) →
      (Measure.pi (fun _ : Fin n => gaussianReal 0 1)).real
        {x | (n : ℝ) * (1 + t) ≤ ∑ i, x i ^ 2} ≤ Real.exp (-(ε ^ 2 * m / 72)) := by
    intro t ht hlog
    have := Q1_upper (Finset.univ : Finset (Fin n)) ht
    rw [Finset.card_fin] at this
    refine this.trans (Real.exp_le_exp.mpr ?_)
    linarith
  have hLoS : ∀ t : ℝ, 0 ≤ t → t < 1 → ε ^ 2 * m / 18 ≤ m * t ^ 2 →
      (Measure.pi (fun _ : Fin n => gaussianReal 0 1)).real
        {x | ∑ i ∈ S, x i ^ 2 ≤ (m : ℝ) * (1 - t)} ≤ Real.exp (-(ε ^ 2 * m / 72)) := by
    intro t ht0 ht1 hlog
    have := Q1_lower S ht0 ht1
    rw [hS] at this
    refine this.trans (Real.exp_le_exp.mpr ?_)
    linarith
  have hLoU : ∀ t : ℝ, 0 ≤ t → t < 1 → ε ^ 2 * m / 18 ≤ n * t ^ 2 →
      (Measure.pi (fun _ : Fin n => gaussianReal 0 1)).real
        {x | ∑ i, x i ^ 2 ≤ (n : ℝ) * (1 - t)} ≤ Real.exp (-(ε ^ 2 * m / 72)) := by
    intro t ht0 ht1 hlog
    have := Q1_lower (Finset.univ : Finset (Fin n)) ht0 ht1
    rw [Finset.card_fin] at this
    refine this.trans (Real.exp_le_exp.mpr ?_)
    linarith
  have hb0 : 0 ≤ Real.exp (-(ε ^ 2 * m / 72)) := (Real.exp_pos _).le
  have hempty : (Measure.pi (fun _ : Fin n => gaussianReal 0 1)).real (∅ : Set (Fin n → ℝ)) ≤
      Real.exp (-(ε ^ 2 * m / 72)) := by
    rw [measureReal_empty]; exact hb0
  have hT0 : ∀ x : Fin n → ℝ, 0 ≤ ∑ i, x i ^ 2 :=
    fun x => Finset.sum_nonneg (fun i _ => sq_nonneg (x i))
  have hXT : ∀ x : Fin n → ℝ, ∑ i ∈ S, x i ^ 2 ≤ ∑ i, x i ^ 2 :=
    fun x => Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S)
      (fun i _ _ => sq_nonneg (x i))
  rcases le_or_gt ε 1 with hε1 | hε1
  · -- small ε
    have hδ0 : 0 ≤ ε / 3 := by positivity
    have hδ1 : ε / 3 < 1 := by linarith
    have hlog : ε ^ 2 / 36 ≤ ε / 3 - Real.log (1 + ε / 3) := by
      apply Q2_coord_log_bound hδ0
      · nlinarith
      · have e1 : ε / 3 - ε ^ 2 / 36 = ε * (1 / 3 - ε / 36) := by ring
        have e2 : (11 / 36 : ℝ) ≤ 1 / 3 - ε / 36 := by linarith
        have e3 : (11 / 36 : ℝ) ^ 2 ≤ (1 / 3 - ε / 36) ^ 2 := pow_le_pow_left₀ (by norm_num) e2 2
        rw [e1, mul_pow]
        nlinarith [sq_nonneg ε]
    have hL0 : 0 ≤ ε / 3 - Real.log (1 + ε / 3) := le_trans (by positivity) hlog
    apply Q2_coord_four _ (A := {x | (m : ℝ) * (1 + ε / 3) ≤ ∑ i ∈ S, x i ^ 2})
      (B := {x | ∑ i ∈ S, x i ^ 2 ≤ (m : ℝ) * (1 - ε / 3)})
      (C := {x | (n : ℝ) * (1 + ε / 3) ≤ ∑ i, x i ^ 2})
      (D := {x | ∑ i, x i ^ 2 ≤ (n : ℝ) * (1 - ε / 3)})
    · intro x hx
      simp only [Set.mem_ofPred_eq] at hx
      by_contra hcon
      simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_le] at hcon
      obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hcon
      exact hx (Q2_coord_pw_small hnR hε hε1 (hT0 x) h1 h2 h3 h4)
    · apply hUpS _ hδ0
      nlinarith
    · apply hLoS _ hδ0 hδ1
      nlinarith
    · apply hUpU _ hδ0
      nlinarith
    · apply hLoU _ hδ0 hδ1
      nlinarith
  · rcases le_or_gt ((n : ℝ)) ((1 + ε) ^ 2 * m) with hbig | hbig
    · apply Q2_coord_four _ (A := ∅) (B := ∅) (C := ∅) (D := ∅) _ hempty hempty hempty hempty
      intro x hx
      simp only [Set.mem_ofPred_eq] at hx
      exact absurd (Q2_coord_pw_big1 hnR hε1 (hT0 x) (hXT x) hbig) hx
    · have ht0 : 0 ≤ (1 + ε) ^ 2 / 2 - 1 := by nlinarith
      have hlog : ε ^ 2 / 36 ≤ ((1 + ε) ^ 2 / 2 - 1) - Real.log (1 + ((1 + ε) ^ 2 / 2 - 1)) := by
        apply Q2_coord_log_bound ht0
        · nlinarith
        · have hA : 17 * ε ^ 2 / 36 ≤ ((1 + ε) ^ 2 / 2 - 1) - ε ^ 2 / 36 := by nlinarith
          have hB : (17 * ε ^ 2 / 36) ^ 2 ≤ (((1 + ε) ^ 2 / 2 - 1) - ε ^ 2 / 36) ^ 2 :=
            pow_le_pow_left₀ (by positivity) hA 2
          nlinarith
      apply Q2_coord_four _ (A := {x | (m : ℝ) * (1 + ((1 + ε) ^ 2 / 2 - 1)) ≤ ∑ i ∈ S, x i ^ 2})
        (B := ∅) (C := ∅) (D := {x | ∑ i, x i ^ 2 ≤ (n : ℝ) * (1 - 1 / 2)})
      · intro x hx
        simp only [Set.mem_ofPred_eq] at hx
        by_contra hcon
        simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_le, Set.mem_empty_iff_false,
          or_false] at hcon
        obtain ⟨h1, h4⟩ := hcon
        exact hx (Q2_coord_pw_big2 hnR hε1 (hT0 x) h1 h4)
      · apply hUpS _ ht0
        nlinarith
      · exact hempty
      · exact hempty
      · apply hLoU _ (by norm_num) (by norm_num)
        have : ε ^ 2 * m ≤ (1 + ε) ^ 2 * m :=
          mul_le_mul_of_nonneg_right (by nlinarith) hmR.le
        nlinarith

/-- Norm of a linear combination of an orthonormal basis of `ℝⁿ`. -/
theorem Q2_reduce_norm_sum {n : ℕ} (b : OrthonormalBasis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)))
    (y : Fin n → ℝ) : ‖∑ i, y i • b i‖ = Real.sqrt (∑ i, y i ^ 2) := by
  have h := b.sum_repr_symm (WithLp.toLp 2 y)
  rw [h, LinearIsometryEquiv.norm_map, EuclideanSpace.norm_eq]
  simp [Real.norm_eq_abs, sq_abs]

/-- (Q2r) Under the standard Gaussian, `(‖Q g‖, ‖g‖)` for an orthogonal projection `Q` of rank `m`
has the law of `(√(Σ_{i∈S} xᵢ²), √(Σ_i xᵢ²))` for i.i.d. standard normal coordinates, `|S| = m`. -/
theorem Q2_reduce {n : ℕ} (Q : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hid : IsIdempotentElem Q) (hsa : IsSelfAdjoint Q) {m : ℕ}
    (hrk : Module.finrank ℝ (LinearMap.range
      (Q : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n))) = m) :
    ∃ S : Finset (Fin n), S.card = m ∧
      ∀ B : Set (ℝ × ℝ), MeasurableSet B →
        (stdGaussian (EuclideanSpace ℝ (Fin n))).real {g | (‖Q g‖, ‖g‖) ∈ B} =
        (Measure.pi (fun _ : Fin n => gaussianReal 0 1)).real
          {x | (Real.sqrt (∑ i ∈ S, x i ^ 2), Real.sqrt (∑ i, x i ^ 2)) ∈ B} := by
  classical
  have hsym : (Q : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n)).IsSymmetric :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hsa
  have hn : Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = n := finrank_euclideanSpace_fin
  set b := hsym.eigenvectorBasis hn with hb
  set μ := hsym.eigenvalues hn with hμ
  have hQb : ∀ i, Q (b i) = μ i • b i := fun i => hsym.apply_eigenvectorBasis hn i
  have hQQ : ∀ v, Q (Q v) = Q v := fun v => by
    have := congrArg
      (fun T : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) => T v) hid.eq
    simpa using this
  have hμ01 : ∀ i, μ i = 0 ∨ μ i = 1 := fun i => by
    have h1 := hQQ (b i)
    rw [hQb, map_smul, hQb, smul_smul] at h1
    have h2 : (μ i * μ i - μ i) • b i = 0 := by rw [sub_smul, h1, sub_self]
    rcases smul_eq_zero.mp h2 with h | h
    · have h3 : μ i * (μ i - 1) = 0 := by rw [mul_sub, mul_one]; exact h
      rcases mul_eq_zero.mp h3 with h' | h'
      · exact Or.inl h'
      · exact Or.inr (by linarith)
    · exact absurd h (b.orthonormal.ne_zero i)
  set S : Finset (Fin n) := Finset.univ.filter (fun i => μ i = 1) with hS
  have hQsum : ∀ x : Fin n → ℝ,
      Q (∑ i, x i • b i) = ∑ i, (if i ∈ S then x i else 0) • b i := by
    intro x
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, hQb, smul_smul]
    rcases hμ01 i with h | h
    · have hi : i ∉ S := by simp [hS, h]
      simp [h, hi]
    · have hi : i ∈ S := by simp [hS, h]
      simp [h, hi]
  refine ⟨S, ?_, ?_⟩
  · have hrange : LinearMap.range
        (Q : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n)) =
        Submodule.span ℝ (Set.range (fun i : S => b i)) := by
      apply le_antisymm
      · rintro v ⟨w, rfl⟩
        rw [← b.sum_repr w]
        change Q (∑ i, b.repr w i • b i) ∈ _
        rw [hQsum]
        refine Submodule.sum_mem _ fun i _ => ?_
        by_cases hi : i ∈ S
        · simp only [hi, if_true]
          exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨i, hi⟩, rfl⟩)
        · simp [hi]
      · rw [Submodule.span_le]
        rintro _ ⟨⟨i, hi⟩, rfl⟩
        refine ⟨b i, ?_⟩
        have h1 : μ i = 1 := (Finset.mem_filter.mp hi).2
        simp only [ContinuousLinearMap.coe_coe]
        rw [hQb, h1, one_smul]
    rw [← hrk, hrange, finrank_span_eq_card]
    · simp
    · exact b.orthonormal.linearIndependent.comp _ Subtype.val_injective
  · intro B hB
    have hmeas : MeasurableSet {g : EuclideanSpace ℝ (Fin n) | (‖Q g‖, ‖g‖) ∈ B} :=
      (by fun_prop : Measurable fun g : EuclideanSpace ℝ (Fin n) => (‖Q g‖, ‖g‖)) hB
    rw [stdGaussian_eq_map_pi_orthonormalBasis b, map_measureReal_apply (by fun_prop) hmeas]
    congr 1
    ext x
    simp only [Set.mem_preimage, Set.mem_ofPred_eq]
    rw [hQsum, Q2_reduce_norm_sum, Q2_reduce_norm_sum]
    have hsq : ∑ i, (if i ∈ S then x i else 0) ^ 2 = ∑ i ∈ S, x i ^ 2 := by
      simp [ite_pow, Finset.sum_ite_mem]
    rw [hsq]

theorem Q3_average_gauss_zero {n : ℕ} (hn : n ≠ 0) :
    stdGaussian (EuclideanSpace ℝ (Fin n)) {0} = 0 := by
  have : Nonempty (Fin n) := ⟨⟨0, Nat.pos_of_ne_zero hn⟩⟩
  have : NullSingletonClass (gaussianReal 0 1) := nullSingletonClass_gaussianReal one_ne_zero
  rw [← map_pi_eq_stdGaussian, Measure.map_apply (by fun_prop) (measurableSet_singleton _)]
  have : (WithLp.toLp 2 : (Fin n → ℝ) → EuclideanSpace ℝ (Fin n)) ⁻¹' {0} = {0} := by
    ext x; simp
  rw [this]
  exact measure_singleton _

theorem Q3_average_inv {Ω : Type} [MeasurableSpace Ω] (Prob : Measure Ω) {n : ℕ}
    (P : Ω → (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)))
    (hmeas : Measurable P)
    (hinv : ∀ U : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n),
      Measure.map (fun ω => (U.toContinuousLinearEquiv : EuclideanSpace ℝ (Fin n) →L[ℝ]
        EuclideanSpace ℝ (Fin n)).comp ((P ω).comp (U.symm.toContinuousLinearEquiv :
          EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)))) Prob
      = Measure.map P Prob)
    (B : Set ℝ) (hB : MeasurableSet B) (θ z : EuclideanSpace ℝ (Fin n)) (h : ‖θ‖ = ‖z‖) :
    Prob {ω | ‖P ω θ‖ ∈ B} = Prob {ω | ‖P ω z‖ ∈ B} := by
  set U : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n) :=
    Submodule.reflection (ℝ ∙ (θ - z))ᗮ with hU
  have hUθ : U θ = z := Submodule.reflection_sub h
  have hUz : U.symm z = θ := by rw [← hUθ]; exact U.symm_apply_apply θ
  have hA : MeasurableSet
      {T : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) | ‖T z‖ ∈ B} :=
    (measurable_norm.comp (ContinuousLinearMap.measurable_apply z)) hB
  have hc : Continuous (fun T : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) =>
      (U.toContinuousLinearEquiv : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)).comp
      (T.comp (U.symm.toContinuousLinearEquiv :
        EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)))) :=
    continuous_const.clm_comp (continuous_id.clm_comp continuous_const)
  have hmeas' : Measurable (fun ω => (U.toContinuousLinearEquiv : EuclideanSpace ℝ (Fin n) →L[ℝ]
        EuclideanSpace ℝ (Fin n)).comp ((P ω).comp (U.symm.toContinuousLinearEquiv :
          EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)))) :=
    hc.measurable.comp hmeas
  have e1 := congrArg (fun μ : Measure (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) =>
    μ {T : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) | ‖T z‖ ∈ B}) (hinv U)
  simp only at e1
  rw [Measure.map_apply hmeas' hA, Measure.map_apply hmeas hA] at e1
  convert e1 using 2
  · ext ω
    simp [hUz]
  · rfl

/-- (Q3) Averaging over a Gaussian direction: a bound valid for every fixed projection of rank `m`
transfers to a uniform random projection applied to a fixed unit vector. -/
theorem Q3_average {Ω : Type} [MeasurableSpace Ω] (Prob : Measure Ω) [IsProbabilityMeasure Prob]
    {n : ℕ} (m : ℕ) (P : Ω → (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)))
    (hP : IsUniformProjection Prob m P) (z : EuclideanSpace ℝ (Fin n)) (hz : ‖z‖ = 1)
    (B : Set ℝ) (hB : MeasurableSet B) (δ : ℝ)
    (hfix : ∀ Q : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n),
      IsIdempotentElem Q → IsSelfAdjoint Q →
      Module.finrank ℝ (LinearMap.range
        (Q : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n))) = m →
      (stdGaussian (EuclideanSpace ℝ (Fin n))).real {g | g ≠ 0 ∧ ‖Q g‖ / ‖g‖ ∈ B} ≤ δ) :
    Prob.real {ω | ‖P ω z‖ ∈ B} ≤ δ := by
  obtain ⟨hmeas, hidem, hsa, hrank, hinv⟩ := hP
  have hn : n ≠ 0 := by
    rintro rfl
    have : z = 0 := Subsingleton.elim _ _
    simp [this] at hz
  set γ := stdGaussian (EuclideanSpace ℝ (Fin n)) with hγ
  have hγ0 : γ {g | g ≠ 0} = 1 := by
    have : {g : EuclideanSpace ℝ (Fin n) | g ≠ 0} = {0}ᶜ := by ext; simp
    rw [this, prob_compl_eq_one_iff (measurableSet_singleton _)]
    exact Q3_average_gauss_zero hn
  have hγm : MeasurableSet {g : EuclideanSpace ℝ (Fin n) | g ≠ 0} :=
    (measurableSet_singleton 0).compl
  have heval : Measurable (fun p : (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) ×
      EuclideanSpace ℝ (Fin n) => p.1 p.2) :=
    isBoundedBilinearMap_apply.continuous.measurable
  have hjoint : Measurable (fun p : Ω × EuclideanSpace ℝ (Fin n) => P p.1 p.2) :=
    heval.comp (hmeas.prodMap measurable_id)
  set S : Set (Ω × EuclideanSpace ℝ (Fin n)) :=
    {p | p.2 ≠ 0 ∧ ‖P p.1 p.2‖ / ‖p.2‖ ∈ B} with hSdef
  have hS : MeasurableSet S :=
    (hγm.preimage measurable_snd).inter ((hjoint.norm.div measurable_snd.norm) hB)
  set c := Prob {ω | ‖P ω z‖ ∈ B} with hc
  have hslice : ∀ g : EuclideanSpace ℝ (Fin n),
      Prob ((fun ω => (ω, g)) ⁻¹' S) = {g | g ≠ 0}.indicator (fun _ => c) g := by
    intro g
    by_cases hg : g = 0
    · have : (fun ω => (ω, g)) ⁻¹' S = ∅ := by
        ext ω; simp [hSdef, hg]
      rw [this, measure_empty, Set.indicator_of_notMem (by simpa using hg)]
    · rw [Set.indicator_of_mem (by simpa using hg)]
      have hg' : ‖g‖ ≠ 0 := norm_ne_zero_iff.mpr hg
      have : (fun ω => (ω, g)) ⁻¹' S = {ω | ‖P ω (‖g‖⁻¹ • g)‖ ∈ B} := by
        ext ω
        simp only [hSdef, Set.mem_preimage, Set.mem_ofPred_eq, map_smul, norm_smul, norm_inv,
          norm_norm]
        rw [div_eq_inv_mul]
        exact ⟨fun h => h.2, fun h => ⟨hg, h⟩⟩
      rw [this, hc]
      exact Q3_average_inv Prob P hmeas hinv B hB _ z
        (by rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hg', hz])
  have key1 : (Prob.prod γ) S = c := by
    rw [Measure.prod_apply_symm hS]
    simp_rw [hslice]
    rw [lintegral_indicator_const hγm, hγ0, mul_one]
  have hgood : ∀ᵐ ω ∂Prob, IsIdempotentElem (P ω) ∧ IsSelfAdjoint (P ω) ∧
      Module.finrank ℝ (LinearMap.range
        (P ω : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n))) = m := by
    filter_upwards [hidem, hsa, hrank] with ω h1 h2 h3 using ⟨h1, h2, h3⟩
  have hδ : 0 ≤ δ := by
    obtain ⟨ω, h1, h2, h3⟩ := hgood.exists
    exact le_trans measureReal_nonneg (hfix (P ω) h1 h2 h3)
  have key2 : (Prob.prod γ) S ≤ ENNReal.ofReal δ := by
    rw [Measure.prod_apply hS]
    calc ∫⁻ ω, γ (Prod.mk ω ⁻¹' S) ∂Prob ≤ ∫⁻ _, ENNReal.ofReal δ ∂Prob := by
          apply lintegral_mono_ae
          filter_upwards [hgood] with ω ⟨h1, h2, h3⟩
          have hle := hfix (P ω) h1 h2 h3
          have : Prod.mk ω ⁻¹' S = {g | g ≠ 0 ∧ ‖P ω g‖ / ‖g‖ ∈ B} := by
            ext g; simp [hSdef]
          rw [this, ← ofReal_measureReal]
          exact ENNReal.ofReal_le_ofReal hle
      _ = ENNReal.ofReal δ := by simp
  rw [measureReal_def]
  exact ENNReal.toReal_le_of_le_ofReal hδ (key1.symm.trans_le key2)

/-- Helper for `solution`: the bound for a fixed orthogonal projection of rank `m`. -/
theorem L_final_hfix {n : ℕ} {m : ℕ} {ε : ℝ} (hε : 0 < ε)
    (Q : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hid : IsIdempotentElem Q) (hsa : IsSelfAdjoint Q)
    (hrk : Module.finrank ℝ (LinearMap.range
      (Q : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n))) = m) :
    (stdGaussian (EuclideanSpace ℝ (Fin n))).real
      {g | g ≠ 0 ∧ ‖Q g‖ / ‖g‖ ∈ {r : ℝ | ¬ ((1 - ε) * Real.sqrt ((m : ℝ) / n) ≤ r ∧
          r ≤ (1 + ε) * Real.sqrt ((m : ℝ) / n))}}
      ≤ 4 * Real.exp (-(ε ^ 2 * m / 72)) := by
  set a := Real.sqrt ((m : ℝ) / n) with ha
  set B' : Set (ℝ × ℝ) := {p | ¬ ((1 - ε) * a * p.2 ≤ p.1 ∧ p.1 ≤ (1 + ε) * a * p.2)}
    with hB'
  have hB'meas : MeasurableSet B' := by
    have h1 : MeasurableSet {p : ℝ × ℝ | (1 - ε) * a * p.2 ≤ p.1} :=
      measurableSet_le (by fun_prop) (by fun_prop)
    have h2 : MeasurableSet {p : ℝ × ℝ | p.1 ≤ (1 + ε) * a * p.2} :=
      measurableSet_le (by fun_prop) (by fun_prop)
    exact (h1.inter h2).compl
  obtain ⟨S, hS, hlaw⟩ := Q2_reduce Q hid hsa hrk
  have hsub : {g : EuclideanSpace ℝ (Fin n) | g ≠ 0 ∧
      ‖Q g‖ / ‖g‖ ∈ {r : ℝ | ¬ ((1 - ε) * a ≤ r ∧ r ≤ (1 + ε) * a)}} ⊆
      {g | (‖Q g‖, ‖g‖) ∈ B'} := by
    intro g hg
    obtain ⟨hg0, hgB⟩ := hg
    have hpos : 0 < ‖g‖ := norm_pos_iff.mpr hg0
    simp only [Set.mem_ofPred_eq, hB'] at hgB ⊢
    rintro ⟨h1, h2⟩
    apply hgB
    constructor
    · rw [le_div_iff₀ hpos]; exact h1
    · rw [div_le_iff₀ hpos]; exact h2
  calc _ ≤ (stdGaussian (EuclideanSpace ℝ (Fin n))).real {g | (‖Q g‖, ‖g‖) ∈ B'} :=
        measureReal_mono hsub
    _ = _ := hlaw B' hB'meas
    _ ≤ _ := Q2_coord S hS hε

/-- Helper for `solution`: the probability bound with `4 exp(-ε² m / 72)`. -/
theorem L_final_main {Ω : Type} [MeasurableSpace Ω] (Prob : Measure Ω)
    [IsProbabilityMeasure Prob]
    {n : ℕ} (m : ℕ) (P : Ω → (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)))
    (hP : IsUniformProjection Prob m P) (z : EuclideanSpace ℝ (Fin n)) {ε : ℝ} (hε : 0 < ε) :
    1 - 4 * Real.exp (-(ε ^ 2 * m / 72)) ≤
      Prob.real {ω | (1 - ε) * Real.sqrt ((m : ℝ) / (n : ℝ)) * ‖z‖ ≤ ‖P ω z‖ ∧
            ‖P ω z‖ ≤ (1 + ε) * Real.sqrt ((m : ℝ) / (n : ℝ)) * ‖z‖} := by
  by_cases hz : z = 0
  · subst hz
    have hset : {ω | (1 - ε) * Real.sqrt ((m : ℝ) / (n : ℝ)) *
          ‖(0 : EuclideanSpace ℝ (Fin n))‖ ≤ ‖P ω 0‖ ∧
          ‖P ω 0‖ ≤ (1 + ε) * Real.sqrt ((m : ℝ) / (n : ℝ)) *
          ‖(0 : EuclideanSpace ℝ (Fin n))‖} = Set.univ := by
      ext ω; simp
    rw [hset, probReal_univ]
    have := Real.exp_pos (-(ε ^ 2 * m / 72))
    linarith
  · have hzpos : 0 < ‖z‖ := norm_pos_iff.mpr hz
    set z₀ := ‖z‖⁻¹ • z with hz₀def
    have hz₀ : ‖z₀‖ = 1 := by
      rw [hz₀def, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hzpos.ne']
    set a := Real.sqrt ((m : ℝ) / n) with ha
    set B : Set ℝ := {r : ℝ | ¬ ((1 - ε) * a ≤ r ∧ r ≤ (1 + ε) * a)} with hBdef
    have hBmeas : MeasurableSet B := by
      have h1 : MeasurableSet {r : ℝ | (1 - ε) * a ≤ r} :=
        measurableSet_le (by fun_prop) (by fun_prop)
      have h2 : MeasurableSet {r : ℝ | r ≤ (1 + ε) * a} :=
        measurableSet_le (by fun_prop) (by fun_prop)
      exact (h1.inter h2).compl
    have hbad : Prob.real {ω | ‖P ω z₀‖ ∈ B} ≤ 4 * Real.exp (-(ε ^ 2 * m / 72)) :=
      Q3_average Prob m P hP z₀ hz₀ B hBmeas _
        (fun Q hid hsa hrk => L_final_hfix hε Q hid hsa hrk)
    have hcover : Set.univ ⊆
        {ω | (1 - ε) * a * ‖z‖ ≤ ‖P ω z‖ ∧ ‖P ω z‖ ≤ (1 + ε) * a * ‖z‖} ∪
          {ω | ‖P ω z₀‖ ∈ B} := by
      intro ω _
      by_cases h : ω ∈ {ω | ‖P ω z₀‖ ∈ B}
      · exact Or.inr h
      · left
        simp only [Set.mem_ofPred_eq, hBdef, not_not] at h
        have hnorm : ‖P ω z₀‖ = ‖P ω z‖ / ‖z‖ := by
          rw [hz₀def, map_smul, norm_smul, norm_inv, norm_norm, inv_mul_eq_div]
        rw [hnorm, le_div_iff₀ hzpos, div_le_iff₀ hzpos] at h
        exact h
    have h1 : (1 : ℝ) ≤
        Prob.real {ω | (1 - ε) * a * ‖z‖ ≤ ‖P ω z‖ ∧ ‖P ω z‖ ≤ (1 + ε) * a * ‖z‖} +
          Prob.real {ω | ‖P ω z₀‖ ∈ B} := by
      calc (1 : ℝ) = Prob.real Set.univ := probReal_univ.symm
        _ ≤ Prob.real (_ ∪ _) := measureReal_mono hcover
        _ ≤ _ := measureReal_union_le _ _
    linarith

/-- Helper for `solution`: the scalar step. -/
theorem L_final_scalar {ε p : ℝ} (m : ℝ)
    (h : 1 - 4 * Real.exp (-(ε ^ 2 * m / 72)) ≤ p) (hp : 0 ≤ p) :
    1 - 2 * Real.exp (-(1 / 144 * ε ^ 2 * m)) ≤ p := by
  set y := Real.exp (-(1 / 144 * ε ^ 2 * m)) with hy
  have hy0 : 0 < y := Real.exp_pos _
  have hsq : Real.exp (-(ε ^ 2 * m / 72)) = y * y := by
    rw [hy, ← Real.exp_add]; ring_nf
  rw [hsq] at h
  by_cases h2 : 1 ≤ 2 * y
  · linarith
  · rw [not_le] at h2
    nlinarith

end HighDimProb.Isoperimetry.RPAux

open HighDimProb.Isoperimetry HighDimProb.Isoperimetry.RPAux in
/-- The target statement (Vershynin, Lemma 5.3.2(b)). -/
theorem solution :
    ∃ c : ℝ, 0 < c ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (Prob : Measure Ω) [IsProbabilityMeasure Prob]
        {n : ℕ} (m : ℕ) (P : Ω → (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)))
        (hP : IsUniformProjection Prob m P) (z : EuclideanSpace ℝ (Fin n)) {ε : ℝ} (hε : 0 < ε),
        1 - 2 * Real.exp (-(c * ε ^ 2 * (m : ℝ))) ≤
          Prob.real {ω | (1 - ε) * Real.sqrt ((m : ℝ) / (n : ℝ)) * ‖z‖ ≤ ‖P ω z‖ ∧
            ‖P ω z‖ ≤ (1 + ε) * Real.sqrt ((m : ℝ) / (n : ℝ)) * ‖z‖} := by
  refine ⟨1 / 144, by norm_num, ?_⟩
  intro Ω _ Prob _ n m P hP z ε hε
  exact L_final_scalar _ (L_final_main Prob m P hP z hε) measureReal_nonneg
