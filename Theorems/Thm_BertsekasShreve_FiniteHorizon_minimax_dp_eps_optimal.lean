import Mathlib
import Definitions.Def_BertsekasShreve_FiniteHorizon_Model
import Definitions.Def_BertsekasShreve_FiniteHorizon_Problem
import Definitions.Def_BertsekasShreve_FiniteHorizon_SpecificModels

namespace BertsekasShreve.FiniteHorizon

open Model

/-- Corollary 3.7.1(a) (Bertsekas & Shreve 1996, p. 51). Let `m` be a model whose mapping is the
minimax mapping (34) of Section 2.3.5 (with `W(x, u)` nonempty for `u ∈ U(x)` and `α > 0`), and
let `J₀(x) = 0` for all `x ∈ S`. If `J*_k(x) > −∞` for all `x ∈ S`, `k = 1, 2, …, N`, then
`J*_N = T^N(J₀)`, and for each `ε > 0` there exists an `N`-stage `ε`-optimal policy. -/
theorem minimax_dp_eps_optimal {S C W : Type*} (m : Model S C) (Wset : S → C → Set W)
    (g : S → C → W → EReal) (f : S → C → W → S) (α : ℝ) (hα : 0 < α)
    (hW : ∀ x, ∀ u ∈ m.U x, (Wset x u).Nonempty)
    (hH : m.H = minimaxH Wset g f α) (J₀ : S → EReal) (hJ₀ : J₀ = fun _ => 0)
    (N : ℕ) (hN : 1 ≤ N)
    (hfin : ∀ x (k : ℕ), 1 ≤ k → k ≤ N → m.optCostN J₀ k x ≠ ⊥) :
    m.optCostN J₀ N = m.T^[N] J₀ ∧
      ∀ ε : ℝ, 0 < ε → ∃ π : m.Policy, m.IsNStageEpsOptimal J₀ N ε π := by sorry

end BertsekasShreve.FiniteHorizon

