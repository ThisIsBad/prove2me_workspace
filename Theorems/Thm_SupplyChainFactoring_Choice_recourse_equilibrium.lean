import Mathlib
import Definitions.Def_SupplyChainFactoring_Choice_Demand
import Definitions.Def_SupplyChainFactoring_Choice_Model

open MeasureTheory Real

namespace SupplyChainFactoring.Choice

/-- Kouvelis–Xu 2021, Proposition 2 (p. 6078). With `ℂ_𝓕` the unique supplier rating at which
`c_𝓕 = p` (stated cross-multiplied, `c e^{(η_s+λ_s)t1} = p Λ_𝓕`): (i) recourse factoring is
feasible iff `Cs > ℂ_𝓕`; (ii) under feasibility the equilibrium exists, is unique, and is
characterized by `p F̄(q) = c_𝓕 [1 + z(q) k(q)]`, `w = c_𝓕 / F̄(q)` with `q ∈ (0, Z)`.
The payment extension `τ` plays no role under recourse factoring. -/
theorem recourse_equilibrium (P : Params) (hP : P.Valid) (μ : Measure ℝ) (f : ℝ → ℝ) (Z : EReal)
    (hD : DemandModel μ f Z) (Cr : ℝ) (hCr : Cr ∈ Set.Ioo P.Cmin P.Cmax)
    (τ : ℝ) (CF : ℝ) (hCF : IsUniqueSolution P.Cmin P.Cmax
      (fun Cs => P.c * exp ((P.η Cs + P.lamS) * P.t1) = P.p * coefF P Cs Cr) CF) :
    ∀ Cs ∈ Set.Ioo P.Cmin P.Cmax,
      (Feasible P μ .recourse Cs Cr τ ↔ CF < Cs) ∧
      (CF < Cs →
        (∃! e : ℝ × ℝ, IsEquilibrium P μ .recourse Cs Cr τ e.1 e.2) ∧
        ∀ w q : ℝ, IsEquilibrium P μ .recourse Cs Cr τ w q ↔
          (0 < q ∧ (q : EReal) < Z ∧
            P.p * Fbar μ q = cF P Cs Cr * (1 + z μ f q * k μ q) ∧
            w = cF P Cs Cr / Fbar μ q)) := by sorry

end SupplyChainFactoring.Choice
