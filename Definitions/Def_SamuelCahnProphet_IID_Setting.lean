import Mathlib

namespace SamuelCahnProphet.IID

open MeasureTheory

/-- `X*ₙ = max(x₁, …, xₙ)` of a sample `x : Fin n → ℝ` (p. 1213). -/
noncomputable def maxV {n : ℕ} [NeZero n] (x : Fin n → ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty x

/-- The threshold rule `t(c)` on a sample (p. 1213): the smallest (0-based) index `i` before the
last with `c ≤ x i`, and the last index `⊤` (the paper's `n`) otherwise. -/
noncomputable def tIdx {n : ℕ} [NeZero n] (x : Fin n → ℝ) (c : ℝ) : Fin n :=
  (Finset.univ.filter (fun i : Fin n => c ≤ x i ∨ i = ⊤)).min' ⟨⊤, by simp⟩

/-- The threshold rule `s(c)` on a sample (p. 1213): the smallest (0-based) index `i` before the
last with `c < x i`, and the last index `⊤` (the paper's `n`) otherwise. -/
noncomputable def sIdx {n : ℕ} [NeZero n] (x : Fin n → ℝ) (c : ℝ) : Fin n :=
  (Finset.univ.filter (fun i : Fin n => c < x i ∨ i = ⊤)).min' ⟨⊤, by simp⟩

/-- The i.i.d. model: the law of `(X₁, …, Xₙ)` with `Xᵢ` i.i.d. of law `μ`, on the coordinate space. -/
noncomputable def iidLaw (μ : Measure ℝ) (n : ℕ) : Measure (Fin n → ℝ) :=
  Measure.pi (fun _ : Fin n => μ)

/-- `E X*ₙ`, in `[0, ∞]`. -/
noncomputable def Emax (μ : Measure ℝ) (n : ℕ) [NeZero n] : ENNReal :=
  ∫⁻ x, ENNReal.ofReal (maxV x) ∂(iidLaw μ n)

/-- `E X_{t(c)}`, in `[0, ∞]`. -/
noncomputable def EstopT (μ : Measure ℝ) (n : ℕ) [NeZero n] (c : ℝ) : ENNReal :=
  ∫⁻ x, ENNReal.ofReal (x (tIdx x c)) ∂(iidLaw μ n)

/-- `E X_{s(c)}`, in `[0, ∞]`. -/
noncomputable def EstopS (μ : Measure ℝ) (n : ℕ) [NeZero n] (c : ℝ) : ENNReal :=
  ∫⁻ x, ENNReal.ofReal (x (sIdx x c)) ∂(iidLaw μ n)

/-- `E⁺X_{t(c)} = E[X_{t(c)} I(X_{t(c)} ≥ c)]` (p. 1213). -/
noncomputable def EplusT (μ : Measure ℝ) (n : ℕ) [NeZero n] (c : ℝ) : ENNReal :=
  ∫⁻ x, (if c ≤ x (tIdx x c) then ENNReal.ofReal (x (tIdx x c)) else 0) ∂(iidLaw μ n)

/-- `E⁺X_{s(c)} = E[X_{s(c)} I(X_{s(c)} > c)]` (p. 1213). -/
noncomputable def EplusS (μ : Measure ℝ) (n : ℕ) [NeZero n] (c : ℝ) : ENNReal :=
  ∫⁻ x, (if c < x (sIdx x c) then ENNReal.ofReal (x (sIdx x c)) else 0) ∂(iidLaw μ n)

/-- `sup_{t ∈ T*ₙ} E X_t`, where `T*ₙ = {t(c), s(c) : c ≥ 0}` (§2, p. 1214). -/
noncomputable def supE (μ : Measure ℝ) (n : ℕ) [NeZero n] : ENNReal :=
  ⨆ (c : ℝ) (_ : 0 ≤ c), max (EstopT μ n c) (EstopS μ n c)

/-- `sup_{t ∈ T*ₙ} E⁺X_t` (§2, p. 1214–1215). -/
noncomputable def supEplus (μ : Measure ℝ) (n : ℕ) [NeZero n] : ENNReal :=
  ⨆ (c : ℝ) (_ : 0 ≤ c), max (EplusT μ n c) (EplusS μ n c)

/-- The law of `Xᵢ⁽ⁿ⁾` in the proof of Theorem 2 (p. 1215): the values `0`, `a`, `1` with
probabilities `1 − (b + c)/n`, `c/n`, `b/n`. It is a probability measure when `0 ≤ b`, `0 ≤ c`,
`b + c ≤ n`, `0 < n`. -/
noncomputable def threePoint (n a b c : ℝ) : Measure ℝ :=
  ENNReal.ofReal (1 - (b + c) / n) • Measure.dirac 0 + ENNReal.ofReal (c / n) • Measure.dirac a
    + ENNReal.ofReal (b / n) • Measure.dirac 1

/-- The proof's `a* = [c(1 − e^{−b}) − b e^{−b}(1 − e^{−c})] / [c(1 − e^{−b−c})]` (p. 1215). Not the
`a*` of the NOTE in §1. -/
noncomputable def aStarIID (b c : ℝ) : ℝ :=
  (c * (1 - Real.exp (-b)) - b * Real.exp (-b) * (1 - Real.exp (-c))) /
    (c * (1 - Real.exp (-b - c)))

/-- `Q(b, c) = 1 + (e^{−b} − e^{−b−c})/(1 − e^{−b−c}) − b(e^{−b} − e^{−b−c})² / [c(1 − e^{−b−c})(1 − e^{−b})]`
(p. 1215). -/
noncomputable def Q (b c : ℝ) : ℝ :=
  1 + (Real.exp (-b) - Real.exp (-b - c)) / (1 - Real.exp (-b - c))
    - b * (Real.exp (-b) - Real.exp (-b - c)) ^ 2 /
      (c * (1 - Real.exp (-b - c)) * (1 - Real.exp (-b)))

end SamuelCahnProphet.IID
