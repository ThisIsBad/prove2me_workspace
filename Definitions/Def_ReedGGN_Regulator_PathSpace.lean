import Mathlib

namespace ReedGGN.Regulator

open MeasureTheory Filter Topology

/-- The paper's `D[0,∞)` (§1.1, p. 5): a path `x : ℝ → ℝ` is right continuous with left limits
on `[0, ∞)`. Only the values on `[0, ∞)` are constrained: `x` is right continuous at every
`t ≥ 0` and has a finite left limit at every `t > 0`. Values at negative times are irrelevant
everywhere in this mission. -/
def IsCadlag (x : ℝ → ℝ) : Prop :=
  (∀ t, 0 ≤ t → ContinuousWithinAt x (Set.Ici t) t) ∧
  (∀ t, 0 < t → ∃ l : ℝ, Tendsto x (𝓝[<] t) (𝓝 l))

/-- The supremum metric on `[0, T]` (§1.1, p. 5): `‖x‖_T = sup_{0 ≤ t ≤ T} |x(t)|`.
The real `⨆` returns `0` on an unbounded family; in this mission it is only applied to
(differences of) càdlàg paths, which are bounded on `[0, T]`, so the value is the true
supremum. For `T < 0` the index set is empty and the value is `0`. -/
noncomputable def supNorm (T : ℝ) (x : ℝ → ℝ) : ℝ :=
  ⨆ t : Set.Icc (0 : ℝ) T, |x t|

/-- The space `D[0,∞)` of càdlàg paths on `[0, ∞)`, as a type. -/
structure Dpath where
  /-- the underlying path -/
  path : ℝ → ℝ
  /-- it is càdlàg on `[0, ∞)` -/
  cadlag : IsCadlag path

/-- The Kolmogorov (cylinder) σ-algebra on `D[0,∞)`: the smallest σ-algebra making every
evaluation `x ↦ x(t)`, `t ≥ 0`, Borel measurable. The paper (p. 35) uses that it equals the
Borel σ-algebra of the Skorohod `J₁` topology (Billingsley 1999, Theorem 16.6). -/
instance Dpath.instMeasurableSpace : MeasurableSpace Dpath :=
  ⨆ t ∈ Set.Ici (0 : ℝ), MeasurableSpace.comap (fun x : Dpath => x.path t) inferInstance

end ReedGGN.Regulator
