import Mathlib
import Definitions.Def_TsengCGD_Global_Basic

namespace TsengCGD.Global

open Filter Topology Finset Matrix
open scoped RealInnerProductSpace

theorem armijo_exists {n : ℕ} (f : Vec n → ℝ) (D : Set (Vec n)) (P : Vec n → ℝ)
    (c : ℝ) (hs : Standing f D P c)
    (x : Vec n) (hx : x ∈ D) (J : Finset (Fin n)) (hJ : J.Nonempty)
    (H : Matrix (Fin n) (Fin n) ℝ) (hH : H.PosDef)
    (d : Vec n) (hd : IsDir f D P c H x J d)
    (β σ γ a₀ : ℝ) (hparams : ArmijoParams β σ γ) (ha₀ : 0 < a₀) :
    (∃ r : ℝ → ℝ, Tendsto (fun a => r a / a) (𝓝[>] (0 : ℝ)) (𝓝 0) ∧
      ∀ a ∈ Set.Ioc (0 : ℝ) 1,
        x + a • d ∈ D ∧
        Fc f P c (x + a • d) ≤ Fc f P c x + a * Delta f P c γ H x d + r a) ∧
    Delta f P c γ H x d ≤ (γ - 1) * qf H d ∧
    (d ≠ 0 → Delta f P c γ H x d < 0) ∧
    ∃ j : ℕ, ArmijoTest f D P c σ γ H x d (a₀ * β ^ j) := by sorry

end TsengCGD.Global

