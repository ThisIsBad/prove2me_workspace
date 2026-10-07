import Mathlib
import Definitions.Def_Gomory69_Asymptotic_GroupPolyhedron

namespace Gomory69.Asymptotic

/-- Proof of THEOREM 4 (p. 462), first step: an irreducible nonnegative integer vector `t`
satisfies `∑_{g ∈ 𝒩} t(g) ≤ |𝒢| − 1` (natural-number subtraction is exact here, as
`|𝒢| ≥ 1`). -/
theorem sum_le_card_sub_one {G : Type*} [AddCommGroup G] [Fintype G] (𝒩 : Finset G)
    (h𝒩 : (0 : G) ∉ 𝒩) (t : ↥𝒩 → ℕ) (ht : IsIrreducible 𝒩 t) :
    ∑ g : ↥𝒩, t g ≤ Fintype.card G - 1 := by sorry

end Gomory69.Asymptotic

