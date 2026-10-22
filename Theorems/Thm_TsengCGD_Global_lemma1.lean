import Mathlib
import Definitions.Def_TsengCGD_Global_Basic

namespace TsengCGD.Global

open Filter Topology Finset Matrix
open scoped RealInnerProductSpace

theorem lemma1 {n : ℕ} (f : Vec n → ℝ) (D : Set (Vec n)) (P : Vec n → ℝ)
    (c : ℝ) (hs : Standing f D P c)
    (x : Vec n) (hx : x ∈ D) (J : Finset (Fin n)) (hJ : J.Nonempty)
    (H : Matrix (Fin n) (Fin n) ℝ) (hH : H.PosDef)
    (d : Vec n) (hd : IsDir f D P c H x J d) :
    (∃ r : ℝ → ℝ, Tendsto (fun a => r a / a) (𝓝[>] (0 : ℝ)) (𝓝 0) ∧
      ∀ a ∈ Set.Ioc (0 : ℝ) 1,
        x + a • d ∈ D ∧
        Fc f P c (x + a • d) ≤
          Fc f P c x + a * (⟪gradient f x, d⟫ + c * P (x + d) - c * P x) + r a) ∧
    ⟪gradient f x, d⟫ + c * P (x + d) - c * P x ≤ -qf H d := by sorry

end TsengCGD.Global

