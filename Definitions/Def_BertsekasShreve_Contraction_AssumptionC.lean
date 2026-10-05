import Mathlib
import Definitions.Def_BertsekasShreve_Contraction_Model

namespace BertsekasShreve.Contraction

open Filter Topology

/-- Assumption C (Contraction Assumption), pp. 52–53, with the scalars `m`, `ρ`, `α` it
introduces made explicit parameters.

* `Bbar` is a closed subset of `B` (sup-norm topology of `ℓ^∞(S, ℝ)`);
* `J₀ ∈ B̄`, and `T(J)`, `T_μ(J)` lie in `B̄` for every `J ∈ B̄`, `μ ∈ M`;
* for every policy the limit (1) exists and is a real number at every `x`;
* `m` is a positive integer, `0 < ρ < 1`, `0 < α`;
* (2): `‖T_μ(J) − T_μ(J')‖ ≤ α ‖J − J'‖` for all `μ ∈ M` and all `J, J' ∈ B` (not only `B̄`);
* (3): `‖(T_{μ₀} ⋯ T_{μ_{m−1}})(J) − (T_{μ₀} ⋯ T_{μ_{m−1}})(J')‖ ≤ ρ ‖J − J'‖` for all
  `μ₀, …, μ_{m−1} ∈ M` and `J, J' ∈ B̄`; the tuple `μ₀, …, μ_{m−1}` is the first `m` entries of a
  policy `π`. -/
structure AssumptionC {S C : Type*} (P : Model S C) (Bbar : Set (BFun S)) (m : ℕ) (ρ α : ℝ) :
    Prop where
  isClosed : IsClosed Bbar
  J0_mem : ∃ J ∈ Bbar, P.J0 = toF J
  T_mem : ∀ J ∈ Bbar, ∃ J' ∈ Bbar, P.T (toF J) = toF J'
  Tmu_mem : ∀ μ : P.Selector, ∀ J ∈ Bbar, ∃ J' ∈ Bbar, P.Tmu μ (toF J) = toF J'
  limit_real : ∀ (π : P.Policy) (x : S), ∃ r : ℝ,
    Tendsto (fun N => P.comp π N P.J0 x) atTop (𝓝 (r : EReal))
  m_pos : 0 < m
  ρ_pos : 0 < ρ
  ρ_lt_one : ρ < 1
  α_pos : 0 < α
  lipschitz : ∀ (μ : P.Selector) (J J' : BFun S),
    SupDistLe (P.Tmu μ (toF J)) (P.Tmu μ (toF J')) (α * ‖J - J'‖)
  contraction : ∀ (π : P.Policy), ∀ J ∈ Bbar, ∀ J' ∈ Bbar,
    SupDistLe (P.comp π m (toF J)) (P.comp π m (toF J')) (ρ * ‖J - J'‖)

end BertsekasShreve.Contraction
