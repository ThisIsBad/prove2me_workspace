import Definitions.Def_OnlineStochMatching_SuggestedMatching_Instance

namespace OnlineStochMatching.SuggestedMatching

variable {A I : Type} [Fintype A] [Fintype I]

/-- Residual reachability among the source, advertisers and types after sending
the integral flow represented by `M`. -/
noncomputable def ResidualStep (inst : Instance A I) (M : Finset (A × I)) :
    Option (A ⊕ I) → Option (A ⊕ I) → Prop
  | none, some (.inl a) => by classical exact (M.filter fun (p : A × I) => p.1 = a).card = 0
  | some (.inl a), some (.inr i) => (a, i) ∈ inst.E ∧ (a, i) ∉ M
  | some (.inr i), some (.inl a) => (a, i) ∈ M
  | _, _ => False

def adInSourceSide (inst : Instance A I) (M : Finset (A × I)) (a : A) : Prop :=
  Relation.ReflTransGen (ResidualStep inst M) none (some (.inl a))

def typeInSourceSide (inst : Instance A I) (M : Finset (A × I)) (i : I) : Prop :=
  Relation.ReflTransGen (ResidualStep inst M) none (some (.inr i))

/-- Advertisers across the canonical residual reachability cut. -/
noncomputable def adsInSinkSide (inst : Instance A I) (M : Finset (A × I)) : Finset A := by
  classical
  exact Finset.univ.filter fun a => ¬ adInSourceSide inst M a

/-- Impression types on the source side of the canonical residual cut. -/
noncomputable def typesInSourceSide (inst : Instance A I) (M : Finset (A × I)) : Finset I := by
  classical
  exact Finset.univ.filter fun i => typeInSourceSide inst M i

end OnlineStochMatching.SuggestedMatching
