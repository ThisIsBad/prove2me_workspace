import Mathlib

open MeasureTheory Filter Topology
open scoped ENNReal

namespace BellWilliams2001.ThresholdPolicy

/-!
Bell and Williams (2001), Section 1.1 (p. 612–613) and Section 2.1 (p. 613–614): path-space
notation shared by every statement of the mission. Time is real; every path is only ever
evaluated at times `t ≥ 0`, and every condition below quantifies over `t ≥ 0` only.
-/

/-- A path `x : [0,∞) → ℝ` is a **Skorokhod path** (a member of `D`, p. 612): it is right
continuous on `[0,∞)` and has finite left limits on `(0,∞)`. Values at negative times are
ignored. -/
def IsCadlag (x : ℝ → ℝ) : Prop :=
  (∀ t : ℝ, 0 ≤ t → ContinuousWithinAt x (Set.Ici t) t) ∧
  (∀ t : ℝ, 0 < t → ∃ l : ℝ, Tendsto x (𝓝[<] t) (𝓝 l))

/-- Partial sums with the paper's index base: `partialSum x n = ∑_{i=1}^{n} x i`, so
`partialSum x 0 = 0` ((2), (4), p. 613; (178), p. 644). The value `x 0` is never used. -/
def partialSum (x : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.Icc 1 n, x i

/-- The counting process of a sequence of partial sums,
`N(t) = sup{n ≥ 0 : X(n) ≤ t}` ((3), (5), p. 613–614; (179), p. 644), computed in `ℕ∞`:
it equals `⊤` when infinitely many partial sums are `≤ t`, never a junk value. -/
noncomputable def renewalCount (X : ℕ → ℝ) (t : ℝ) : ℕ∞ :=
  ⨆ (n : ℕ) (_ : X n ≤ t), (n : ℕ∞)

/-- `‖f − g‖_t = sup_{s ∈ [0,t]} |f(s) − g(s)|` ((1), p. 612) for `ℝ^m`-valued paths, with the
paper's norm `|x| = ∑ᵢ |xᵢ|`. The supremum is taken in `[0,∞]`, so it is never a junk value. -/
noncomputable def supDist {m : ℕ} (f g : ℝ → Fin m → ℝ) (t : ℝ) : ℝ≥0∞ :=
  ⨆ (s : ℝ) (_ : s ∈ Set.Icc 0 t), ENNReal.ofReal (∑ i, |f s i - g s i|)

/-- **Uniform convergence on compact time intervals in probability** (p. 613): processes
`Z n` defined on `(Ω, P)` converge u.o.c. in probability to the deterministic path `z` if
`P(‖Z n − z‖_t ≥ ε) → 0` as `n → ∞` for every `ε > 0` and every `t ≥ 0`. -/
def UocInProb {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {m : ℕ}
    (Z : ℕ → Ω → ℝ → Fin m → ℝ) (z : ℝ → Fin m → ℝ) : Prop :=
  ∀ t : ℝ, 0 ≤ t → ∀ ε : ℝ, 0 < ε →
    Tendsto (fun n => P {ω | ENNReal.ofReal ε ≤ supDist (Z n ω) z t}) atTop (𝓝 0)

/-- **Convergence in distribution to a process with continuous paths, in coupling form.**
Processes `Z n` on `(Ω, P)` and `Zlim` on `(Ω', P')`, all `ℝ^m`-valued with time `t ≥ 0`, are
related by: there are a probability space `(Ω'', P'')` and processes `Y n`, `Ylim` on it such that
`Y n` has the law of `Z n` for all large `n` and `Ylim` has the law of `Zlim` (laws of the paths restricted to
`[0,∞)`, on the product σ-algebra, which is the Borel σ-algebra of `D^m`, p. 612), every path of
every `Y n` is a Skorokhod path, and almost surely `Y n → Ylim` uniformly on compact time
intervals. When `Zlim` has continuous paths and the `Z n` have Skorokhod paths this is equivalent
to `Z n ⟹ Zlim` in `D^m` with the `J₁` topology (Skorokhod representation in one direction; a.s.
u.o.c. convergence implies a.s. `J₁` convergence, hence weak convergence, in the other). Only the laws of the `Z n` for large `n` matter, as for weak convergence. -/
def CouplingConverges {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) (P' : Measure Ω') {m : ℕ}
    (Z : ℕ → Ω → ℝ → Fin m → ℝ) (Zlim : Ω' → ℝ → Fin m → ℝ) : Prop :=
  ∃ (Ω'' : Type) (_ : MeasurableSpace Ω'') (P'' : Measure Ω'')
    (Y : ℕ → Ω'' → ℝ → Fin m → ℝ) (Ylim : Ω'' → ℝ → Fin m → ℝ),
    IsProbabilityMeasure P'' ∧
    (∀ᶠ n in atTop, ProbabilityTheory.IdentDistrib (fun ω (t : NNReal) => Y n ω t)
      (fun ω (t : NNReal) => Z n ω t) P'' P) ∧
    ProbabilityTheory.IdentDistrib (fun ω (t : NNReal) => Ylim ω t)
      (fun ω (t : NNReal) => Zlim ω t) P'' P' ∧
    (∀ n ω (i : Fin m), IsCadlag (fun t => Y n ω t i)) ∧
    ∀ᵐ ω ∂P'', ∀ t : ℝ, 0 ≤ t → Tendsto (fun n => supDist (Y n ω) (Ylim ω) t) atTop (𝓝 0)

end BellWilliams2001.ThresholdPolicy
