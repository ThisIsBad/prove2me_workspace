import Mathlib

namespace LeblSCV.BallPolydisc

/-- Definition 1.4.3 (Lebl, p. 33), for a map `f : U → V` between subsets `U ⊆ X`, `V ⊆ Y` with
their subspace topologies: `f` maps `U` into `V`, is continuous on `U`, and the preimage in `U`
of every compact `K ⊆ V` is compact. (A subset of `V` is compact in the subspace topology of `V`
iff it is compact in `Y`, and likewise for `U`.) -/
def IsProperMapOn {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) (U : Set X) (V : Set Y) : Prop :=
  Set.MapsTo f U V ∧ ContinuousOn f U ∧
    ∀ K : Set Y, K ⊆ V → IsCompact K → IsCompact (U ∩ f ⁻¹' K)

end LeblSCV.BallPolydisc
