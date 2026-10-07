import Definitions.Def_UnderstandingML_Online
import Definitions.Def_WeightedMajority_Anomalies_Opt

/-!
# Littlestone and Warmuth, *The Weighted Majority Algorithm* (1994), §8: the sequence class S_η

Littlestone, Warmuth, *The Weighted Majority Algorithm*, Inform. and Comput. 108 (1994),
pp. 249–250, §8. A trial is a pair `(x, y)` of an instance and a binary label; a sequence of
trials is `S : Fin T → X × Bool`. The number of anomalies of `S` with respect to `f`
(`WeightedMajority.Anomalies.anomalies`) is the number of trials inconsistent with `f`; `S ∈ S_η`
when some `f ∈ F` has at most `η` anomalies on `S`. The deterministic optimum `opt(F, η)` is the
shared definition `WeightedMajority.Anomalies.opt`.
-/

namespace WeightedMajority.RandAnomalies

open UnderstandingML

variable {X : Type*}

/-- `S ∈ S_η` (p. 250): the sequence `S` has at most `η` anomalies with respect to the pool `F`,
i.e. some `f ∈ F` has at most `η` anomalies on `S` (the same predicate as
`WeightedMajority.Anomalies.HasAtMostAnomalies`). -/
def InSEta (F : Set (X → Bool)) (η : ℕ) {T : ℕ} (S : Fin T → X × Bool) : Prop :=
  ∃ f ∈ F, WeightedMajority.Anomalies.anomalies f S ≤ η

end WeightedMajority.RandAnomalies
