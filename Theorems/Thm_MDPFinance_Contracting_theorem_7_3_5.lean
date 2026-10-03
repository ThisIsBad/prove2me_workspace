import Mathlib
import Definitions.Def_MDPFinance_Contracting_Model
import Definitions.Def_MDPFinance_Contracting_Value
import Definitions.Def_MDPFinance_Contracting_Bounding

open MeasureTheory ProbabilityTheory

namespace MDPFinance.Contracting

/-- **Theorem 7.3.5 (Structure Theorem)** (Bäuerle–Rieder, p. 207, PDF 218, the goal theorem of
this mission). Let `b` be a bounding function and `\beta\alpha_b < 1`. If there exists a closed
subset `IM \subset IB_b` (closedness stated sequentially in the `\|\cdot\|_b`-norm, since no
pre-built `MetricSpace` instance for the weighted-sup-norm space is introduced in this mission)
and a set `\Delta \subset F` such that (i) `0 \in IM`, (ii) `T : IM \to IM` (via the real-valued
`T'`), (iii) for all `v \in IM`
there exists a maximizer `f \in \Delta` of `v`, then it holds: a) `J_\infty \in IM`, `J_\infty =
TJ_\infty` and `J_\infty = J` (Value Iteration). b) `J_\infty` is the unique fixed point of `T` in
`IM`. c) `J_\infty` is the smallest `r`-superharmonic function `v \in IM`, i.e. `J_\infty` is the
smallest function `v \in IM` with `v \ge Tv` (`r`-superharmonic: `Tv ≤ v`). d) Let `g \in IM`. Then `\|J_\infty - T^ng\|_b \le
\frac{(\beta\alpha_b)^n}{1-\beta\alpha_b}\|Tg-g\|_b`. e) There exists a maximizer `f \in \Delta`
of `J_\infty`, and every maximizer `f^*` of `J_\infty` defines an optimal stationary policy
`(f^*,f^*,\dots)`. `J_\infty` is identified with its real-valued representative in `IM \subset
IB_b` throughout (cast to `EReal` via the coercion where compared against `Jinf`/`Jlim`). -/
theorem theorem_7_3_5 {E A : Type*} [MeasurableSpace E] [MeasurableSpace A] (M : MarkovDecisionModel E A)
    (b : E → ℝ) (cr αb : ℝ) (hb : IsBoundingFunction M b cr αb) (hαb : M.β * αb < 1)
    (IMs : Set (E → ℝ)) (hIMsub : IMs ⊆ IBb b)
    (hIMclosed : ∀ (vn : ℕ → E → ℝ) (v : E → ℝ), (∀ n, vn n ∈ IMs) → v ∈ IBb b →
      Filter.Tendsto (fun n => normb b fun x => vn n x - v x) Filter.atTop (nhds 0) → v ∈ IMs)
    (Δ : Set (E → A))
    (h0 : (0 : E → ℝ) ∈ IMs) (hTmaps : ∀ v ∈ IMs, (fun x => T' M v x) ∈ IMs)
    (hmax : ∀ v ∈ IMs, ∃ f ∈ Δ, IsMaximizerOf M (fun x => (v x : EReal)) f) :
    (∃ v ∈ IMs, (∀ x, Jinf M x = (v x : EReal)) ∧ (∀ x, T' M v x = v x) ∧
        ∀ x, Jinf M x = Jlim M x) ∧
      (∀ v ∈ IMs, (∀ x, T' M v x = v x) → ∀ x, (v x : EReal) = Jinf M x) ∧
      (∀ v ∈ IMs, (∀ x, T' M v x ≤ v x) → ∀ x, Jinf M x ≤ (v x : EReal)) ∧
      (∀ g ∈ IMs, ∀ n : ℕ,
        normb b (fun x => (Jinf M x).toReal - (T' M)^[n] g x) ≤
          (M.β * αb) ^ n / (1 - M.β * αb) * normb b (fun x => T' M g x - g x)) ∧
      ((∃ f ∈ Δ, IsMaximizerOf M (Jinf M) f) ∧
        ∀ fstar : E → A, IsMaximizerOf M (Jinf M) fstar →
          ∀ x, Jinfpi M M.r (fun _ => fstar) x = Jinf M x) := by sorry

end MDPFinance.Contracting
