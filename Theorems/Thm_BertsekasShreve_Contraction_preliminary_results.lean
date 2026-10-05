import Mathlib
import Definitions.Def_BertsekasShreve_Contraction_Model
import Definitions.Def_BertsekasShreve_Contraction_AssumptionC

namespace BertsekasShreve.Contraction

open Filter Topology

/-- Proposition 4.1, p. 53. Under Assumption C:
(a) for every `J ∈ B̄` and `π ∈ Π`, `J_π = lim_N (T_{μ₀} ⋯ T_{μ_{N−1}})(J₀) = lim_N (T_{μ₀} ⋯ T_{μ_{N−1}})(J)`
pointwise;
(b) for each positive integer `N` and `J ∈ B̄`, `inf_π (T_{μ₀} ⋯ T_{μ_{N−1}})(J) = T^N(J)`, and
`J*_N = T^N(J₀)`;
(c) `‖T^m(J) − T^m(J')‖ ≤ ρ‖J − J'‖` and `‖T_μ^m(J) − T_μ^m(J')‖ ≤ ρ‖J − J'‖` for `J, J' ∈ B̄`. -/
theorem preliminary_results {S C : Type*} (P : Model S C) (Bbar : Set (BFun S)) (m : ℕ)
    (ρ α : ℝ) (hC : AssumptionC P Bbar m ρ α) :
    (∀ J ∈ Bbar, ∀ (π : P.Policy) (x : S),
      Tendsto (fun N => P.comp π N P.J0 x) atTop (𝓝 (P.Jpi π x)) ∧
      Tendsto (fun N => P.comp π N (toF J) x) atTop (𝓝 (P.Jpi π x))) ∧
    (∀ N : ℕ, 1 ≤ N → ∀ J ∈ Bbar,
      (fun x => ⨅ π : P.Policy, P.comp π N (toF J) x) = P.T^[N] (toF J)) ∧
    (∀ N : ℕ, 1 ≤ N → P.JNstar N = P.T^[N] P.J0) ∧
    (∀ J ∈ Bbar, ∀ J' ∈ Bbar,
      SupDistLe (P.T^[m] (toF J)) (P.T^[m] (toF J')) (ρ * ‖J - J'‖)) ∧
    (∀ μ : P.Selector, ∀ J ∈ Bbar, ∀ J' ∈ Bbar,
      SupDistLe ((P.Tmu μ)^[m] (toF J)) ((P.Tmu μ)^[m] (toF J')) (ρ * ‖J - J'‖)) := by sorry

end BertsekasShreve.Contraction

