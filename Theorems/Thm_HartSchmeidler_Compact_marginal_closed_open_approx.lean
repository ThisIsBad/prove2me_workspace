import Definitions.Def_HartSchmeidler_Compact_Game

namespace HartSchmeidler.Compact

open MeasureTheory

/-- Proof of Theorem 3, p. 24, with footnote 16: for a regular probability measure `p` on the
compact space `S`, every Borel set `Rⁱ ⊆ Sⁱ` lies between a closed `Fⁱ` and an open `Gⁱ` with
`p((Gⁱ \ Fⁱ) × S⁻ⁱ) < ε`. -/
theorem marginal_closed_open_approx {ι : Type*} {S : ι → Type*}
    [∀ i, TopologicalSpace (S i)] [∀ i, CompactSpace (S i)] [∀ i, T2Space (S i)]
    [∀ i, MeasurableSpace (S i)] [∀ i, BorelSpace (S i)]
    (p : Measure (Profile S)) [IsProbabilityMeasure p] (hp : p.Regular)
    (i : ι) (R : Set (S i)) (hR : MeasurableSet R) (ε : ℝ) (hε : 0 < ε) :
    ∃ F G : Set (S i), IsClosed F ∧ IsOpen G ∧ F ⊆ R ∧ R ⊆ G ∧
      p ((fun s : Profile S => s i) ⁻¹' (G \ F)) < ENNReal.ofReal ε := by sorry

end HartSchmeidler.Compact

