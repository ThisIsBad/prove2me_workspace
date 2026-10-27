import Definitions.Def_PricingWithTips3DM_3a64b523d21161fe1251d130Part6
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

namespace PricingWithTips.FixedShape3DM

open Hardness Hardness.Cert Hardness.Sat3dm

theorem matching_normalized_iff (input : List CLRS.Chapter34.CNFSym) :
    MATCHING_3D (abstractInstance input) ↔
      MATCHING_3D (normalizedInstance input) := by
  let e := (wEquiv input).prodCongr
    ((slotEquiv input).prodCongr (slotEquiv input))
  let f := fun t : Sat3dm.Trip (variableList input).length
      (paddedCNF input).length =>
    ((wMap input) t.1, ((slotMap input) t.2.1, (slotMap input) t.2.2))
  have hef : ∀ t, e t = f t := by
    rintro ⟨w, x, y⟩
    apply Prod.ext
    · apply Fin.ext
      exact SatToMatching3DCode.extEquivFin_val _ _ w
    · apply Prod.ext <;> apply Fin.ext
      · exact SatToMatching3DCode.slotEquivFin_val _ _ x
      · exact SatToMatching3DCode.slotEquivFin_val _ _ y
  apply matching3D_iff_of_equiv (wEquiv input) (slotEquiv input) (slotEquiv input)
  intro t
  change t ∈ triples input ↔ e t ∈ (triples input).image f
  rw [hef t]
  constructor
  · exact Finset.mem_image_of_mem f
  · intro ht
    obtain ⟨u, hu, heu⟩ := Finset.mem_image.mp ht
    have hut : u = t := e.injective ((hef u).trans (heu.trans (hef t).symm))
    subst u
    exact hu
end PricingWithTips.FixedShape3DM
