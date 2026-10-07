import Mathlib
import Definitions.Def_UnderstandingML_Online

namespace WeightedMajority.Anomalies

open UnderstandingML

/-- The number of **anomalies** of the sequence of trials `S` with respect to the function `f`
(Littlestone–Warmuth §8, p. 249): the number of trials `t` whose label `(S t).2` differs from
`f` at the instance `(S t).1`. -/
noncomputable def anomalies {X : Type*} (f : X → Bool) {T : ℕ} (S : Fin T → X × Bool) : ℕ :=
  (Finset.univ.filter (fun t : Fin T ↦ f (S t).1 ≠ (S t).2)).card

/-- `S ∈ S_η` (§8, p. 250): the sequence `S` has at most `η` anomalies with respect to the pool
`F`, i.e. the minimum over `f ∈ F` of the number of anomalies of `S` with respect to `f` is at
most `η`; equivalently some `f ∈ F` has at most `η` anomalies on `S`. -/
def HasAtMostAnomalies {X : Type*} (F : Set (X → Bool)) (η : ℕ) {T : ℕ}
    (S : Fin T → X × Bool) : Prop :=
  ∃ f ∈ F, anomalies f S ≤ η

/-- `opt(F, η)` (§8, p. 250): the minimum over all deterministic online prediction algorithms
`A` of the maximum, over all finite sequences of trials `S ∈ S_η`, of the number of mistakes
made by `A` on `S`. Valued in `ℕ∞`, so it is `⊤` when every algorithm can be forced to make
arbitrarily many mistakes. -/
noncomputable def opt {X : Type*} (F : Set (X → Bool)) (η : ℕ) : ℕ∞ :=
  ⨅ A : OnlineAlg X Bool,
    ⨆ (T : ℕ) (S : Fin T → X × Bool) (_ : HasAtMostAnomalies F η S), (mistakes A S : ℕ∞)

end WeightedMajority.Anomalies
