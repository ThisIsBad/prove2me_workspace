import Definitions.Def_PricingWithTips_ThreeDM

namespace PricingWithTips

/-- A triple in an equal-cardinality three-dimensional matching instance. -/
abbrev ThreeDMTriple (n : ℕ) := Fin n × Fin n × Fin n

/-- Every vertex in the codomain occurs in exactly one selected triple. -/
def IsExactCover3DM {α β : Type*} (M : Finset α) (p : α → β) : Prop :=
  ∀ b : β, ∃! t : α, t ∈ M ∧ p t = b

/-- A finite set of triples contains a perfect three-dimensional matching. -/
def HasPerfectFinset3DM (n : ℕ) (T : Finset (ThreeDMTriple n)) : Prop :=
  ∃ M : Finset (ThreeDMTriple n), M ⊆ T ∧
    IsExactCover3DM M Prod.fst ∧
    IsExactCover3DM M (fun t => t.2.1) ∧
    IsExactCover3DM M (fun t => t.2.2)

end PricingWithTips
