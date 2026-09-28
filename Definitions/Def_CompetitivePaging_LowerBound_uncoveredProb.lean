import Mathlib
import Definitions.Def_KServer_model
import Definitions.Def_KServer_randomized

namespace CompetitivePaging.LowerBound

open MeasureTheory

/-- The adversary's **probability vector** (Fiat et al. 1991, §5, proof of Theorem 4, p. 7):
`uncoveredProb A σ i` is the probability `p_i`, over the coin outcomes of the randomized online
algorithm `A`, that vertex `i` is **not** covered by a server of `A` after `A` has served the
request sequence `σ`. It is the measure of the set of outcomes `ω` for which `i` is not among
the positions of the configuration `(A.alg ω).conf σ`, converted to a real number (the measure
is a probability measure, so the value lies in `[0, 1]`). -/
noncomputable def uncoveredProb {k : ℕ} {M : Type*} [MetricSpace M]
    (A : KServer.RandomizedAlgorithm k M) (σ : List M) (i : M) : ℝ :=
  (A.μ {ω | i ∉ Set.range ((A.alg ω).conf σ)}).toReal

end CompetitivePaging.LowerBound
