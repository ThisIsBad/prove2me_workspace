import Mathlib
import Definitions.Def_VapnikChervonenkis_Shared_index
import Definitions.Def_VapnikChervonenkis_Shared_growthFunction

namespace VapnikChervonenkis.GrowthFunction

theorem aux_iltp_bound {X : Type*} (S : Set (Set X)) {r : ℕ} (x : Fin r → X) :
    Shared.index S x ≤ 2 ^ r := by
  classical
  unfold Shared.index
  calc _ ≤ (Finset.univ : Finset (Finset (Fin r))).card := Finset.card_filter_le _ _
    _ = 2 ^ r := by simp [Finset.card_univ, Fintype.card_finset]

end VapnikChervonenkis.GrowthFunction

open VapnikChervonenkis.GrowthFunction
open VapnikChervonenkis

theorem solution {X : Type*} (S : Set (Set X)) {r : ℕ} (x : Fin r → X) :
    Shared.index S x ≤ 2 ^ r := aux_iltp_bound S x
