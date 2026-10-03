import Mathlib
import Definitions.Def_MDPFinance_DividendProblems_MDM
import Definitions.Def_MDPFinance_DividendProblems_Dividend

open scoped ENNReal NNReal
open MeasureTheory ProbabilityTheory Filter

namespace MDPFinance.DividendProblems

/-- Lemma 9.2.2 (Bäuerle–Rieder, p. 273, PDF 283). a) `b(x) := 1 + x` for `x \ge 0`, `b(x) := 0`
for `x < 0`, is a bounding function for the dividend model (for some constants `c_r, \alpha_b`),
with `T_\circ^n b \le \beta^n b + n\,\mathbb E Z^+`. b) For `x \ge 0`, `\delta(x) \le x + \beta\,
\mathbb E Z^+/(1-\beta)`, hence `\delta \in IB_b` — where `\delta = J_\infty` for this positive
model (the book's own remark in the proof), so `J_\infty` is finite everywhere and `b`-bounded. -/
theorem lemma_9_2_2 (M : DividendModel) :
    (∃ cr αb : ℝ, IsBoundingFunction M.toMDM
        (fun x : ℤ => if 0 ≤ x then 1 + (x : ℝ) else 0) cr αb) ∧
      (∀ n : ℕ, ∀ x : ℤ,
        (TcircL M.toMDM)^[n] (fun x : ℤ => ENNReal.ofReal (if 0 ≤ x then 1 + (x : ℝ) else 0)) x ≤
          ENNReal.ofReal (M.β ^ n * (if 0 ≤ x then 1 + (x : ℝ) else 0) + n * M.EZplus)) ∧
      (∀ x : ℤ, 0 ≤ x → M.Jinf x ≤ ENNReal.ofReal ((x : ℝ) + M.β * M.EZplus / (1 - M.β))) ∧
      (∀ x, M.Jinf x < ⊤) ∧
      (fun x => (M.Jinf x).toReal) ∈ IBb (fun x : ℤ => if 0 ≤ x then 1 + (x : ℝ) else 0) := by sorry

end MDPFinance.DividendProblems
