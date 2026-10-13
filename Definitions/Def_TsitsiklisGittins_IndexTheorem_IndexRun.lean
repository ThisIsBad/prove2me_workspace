import Mathlib
import Definitions.Def_TsitsiklisGittins_IndexTheorem_Reduction

namespace TsitsiklisGittins.IndexTheorem

namespace SemiMarkovBandit

variable {n : ℕ} {X : Fin n → Type} [∀ i, Fintype (X i)] [∀ i, DecidableEq (X i)]
  [∀ i, MeasurableSpace (X i)] [∀ i, MeasurableSingletonClass (X i)]

/-- A run of the INDEX ALGORITHM (pp. 197–198) on `B`, picking the states in the order `seq` and
assigning the indices `γ`: `seq` lists every state of `𝒳` exactly once, and for every `k`, at the
stage obtained from the initial one by removing `seq[0], …, seq[k-1]` in turn,
(a) `seq[k]` is still present and its rate is the maximum of the rates of all present states,
and `γ(seq[k])` is that rate; (b) the next stage removes `seq[k]` (reduction of its bandit).
Ties in step (a) may be broken arbitrarily: every such choice is a run. -/
def IsIndexRun (B : SemiMarkovBandit n X) (seq : List (Σ i, X i)) (γ : (Σ i, X i) → ℝ) : Prop :=
  seq.Nodup ∧ (∀ q, q ∈ seq) ∧
    ∀ (k : ℕ) (hk : k < seq.length),
      seq[k] ∈ (B.stageAfter (seq.take k)).alive ∧
      (∀ q ∈ (B.stageAfter (seq.take k)).alive,
        (B.stageAfter (seq.take k)).rate q ≤ (B.stageAfter (seq.take k)).rate seq[k]) ∧
      γ seq[k] = (B.stageAfter (seq.take k)).rate seq[k]

end SemiMarkovBandit

end TsitsiklisGittins.IndexTheorem
