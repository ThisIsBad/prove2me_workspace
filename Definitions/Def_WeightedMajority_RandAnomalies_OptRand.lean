import Definitions.Def_WeightedMajority_RandAnomalies_Anomalies

/-!
# Littlestone and Warmuth (1994), §8: the randomized optimum opt_RAND(F, η)

Littlestone, Warmuth, *The Weighted Majority Algorithm*, Inform. and Comput. 108 (1994),
p. 250, §8 and p. 252, proof of Theorem 8.2. The randomization of a randomized algorithm is
independent of the sequence, so on a fixed sequence its behaviour at trial `t` is summarized by
`pₜ ∈ [0,1]`, the probability that it predicts `1` given the preceding instances and labels and
the current instance (not conditioned on its own earlier predictions, p. 252). Its expected
number of mistakes on `S` is then `∑ₜ |pₜ − yₜ|`, which is `cumLoss` of `UnderstandingML_Online`.
Conversely every map `(history, x) ↦ p ∈ [0,1]` is realized by the randomized algorithm that
predicts `1` with probability `p` using fresh independent coins at each trial.
-/

open scoped ENNReal

namespace WeightedMajority.RandAnomalies

open UnderstandingML

variable {X : Type*}

/-- A real-valued online algorithm is a **randomized prediction algorithm** when each of its
outputs is a probability, `A hist x ∈ [0,1]`: the probability of predicting `1`. -/
def IsRandAlg (A : OnlineAlgR X) : Prop :=
  ∀ (hist : List (X × Bool)) (x : X), A hist x ∈ Set.Icc (0 : ℝ) 1

/-- `opt_RAND(F, η)` (p. 250): the infimum over all randomized algorithms `A` of the supremum,
over all finite sequences `S ∈ S_η`, of the expected number of mistakes `∑ₜ |pₜ − yₜ|` of `A`
on `S`, valued in `[0, ∞]`. -/
noncomputable def optRand (F : Set (X → Bool)) (η : ℕ) : ℝ≥0∞ :=
  ⨅ (A : OnlineAlgR X) (_ : IsRandAlg A),
    ⨆ (T : ℕ) (S : Fin T → X × Bool) (_ : InSEta F η S), ENNReal.ofReal (cumLoss A S)

end WeightedMajority.RandAnomalies
