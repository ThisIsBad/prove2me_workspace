import Mathlib

namespace OnlineSetCover.LowerBound

/-- The set `F_{R,I}` of §4 (Alon et al. 2009, p. 368) on the block ground set
`Fin B × Fin (2^k)`: the element `(b, j)` is element `j` of block `X_{b+1}`, and its bit number
`t + 1` is `Nat.testBit j t`. For a set `R` of block indices and a choice `I` of a bit location
`I b` for every block, `F_{R,I}` is the union over `b ∈ R` of `X_b(I b)`, the elements of block
`b` whose bit `I b` is on. Only the values of `I` on `R` matter. -/
def blockSet {k B : ℕ} (R : Finset (Fin B)) (I : Fin B → Fin k) : Finset (Fin B × Fin (2 ^ k)) :=
  Finset.univ.filter (fun p => p.1 ∈ R ∧ p.2.val.testBit (I p.1).val)

/-- The family `𝓕` of §4 (p. 368–369): all sets `F_{R,I}` with `R` an `r`-element subset of the
`k r²` blocks and `I` a choice of one of the `k` bit locations in each block of `R`. The ground
set is the `k r²` disjoint blocks of `2^k` elements each, `Fin (k * r ^ 2) × Fin (2 ^ k)`. -/
def blockFamily (k r : ℕ) : Finset (Finset (Fin (k * r ^ 2) × Fin (2 ^ k))) :=
  ((Finset.univ.powersetCard r) ×ˢ (Finset.univ : Finset (Fin (k * r ^ 2) → Fin k))).image
    (fun RI => blockSet RI.1 RI.2)

end OnlineSetCover.LowerBound
