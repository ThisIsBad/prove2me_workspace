import Mathlib
import Definitions.Def_FoundationsML_RademacherVC_HasVCDim

namespace FoundationsML.RademacherVC

/-- Theorem 3.17 (Sauer's lemma; Mohri, Rostamizadeh & Talwalkar, *Foundations of Machine
Learning*, 2nd ed., MIT Press 2018, p. 41, PDF p. 58). Let `H` be a hypothesis set with
`VCdim(H) = d`. Then, for all `m ∈ ℕ`, `Π_H(m) ≤ ∑_{i=0}^{d} C(m,i)`. -/
theorem sauer_lemma
    {X : Type*} (H : Set (X → Bool)) (d : ℕ) (hH : HasVCDim H d) (m : ℕ) :
    GrowthFunction H m ≤ ∑ i ∈ Finset.range (d + 1), Nat.choose m i := by sorry

end FoundationsML.RademacherVC
