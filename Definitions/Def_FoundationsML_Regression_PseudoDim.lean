import Mathlib
import Definitions.Def_FoundationsML_Regression_Shatters

namespace FoundationsML.Regression

/-- `G` has pseudo-dimension `d` (Mohri, Rostamizadeh & Talwalkar, *Foundations of Machine
Learning*, 2nd ed., MIT Press 2018, Definition 11.5, p. 271, PDF p. 288):
`Pdim(G) = max{m : some m-point set is shattered by G}`.

**Formalization Note.** `PseudoDim G d` states `d` is such a maximum directly: some `d`-point
tuple is shattered, and every `m`-point tuple shattered by `G` has `m ≤ d`. As with chunk
`03-rademacher-vc`'s `HasVCDim`, this `Prop`-valued definition does not assign a value in the
case of an unboundedly shatterable `G` (`Pdim(G) = +∞`); every theorem using it takes
`PseudoDim G d` as an explicit hypothesis. This is a genuinely different (real-valued,
threshold-witnessed) combinatorial notion from `HasVCDim`, not a relabeling of it. -/
def PseudoDim {Z : Type*} (G : Set (Z → ℝ)) (d : ℕ) : Prop :=
  (∃ z : Fin d → Z, Shatters G z) ∧ ∀ m : ℕ, (∃ z : Fin m → Z, Shatters G z) → m ≤ d

end FoundationsML.Regression
