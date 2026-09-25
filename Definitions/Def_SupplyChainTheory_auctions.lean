import Mathlib

namespace SupplyChainTheory

/-! ### The VCG auction as a cooperative game, Sect. 15.4.3 -/

/-- Players are `Fin (n+1)`: `0` is the auctioneer and `1, …, n` are the bidders. A function on
coalitions is a coalitional value function when coalitions without the auctioneer create no
value and adding players never lowers the value. -/
def IsCoalitionalValue {n : ℕ} (V : Finset (Fin (n + 1)) → ℝ) : Prop :=
  (∀ T, (0 : Fin (n + 1)) ∉ T → V T = 0) ∧ Monotone V

/-- `V(T)` for the combinatorial auction: the optimal value of the auctioneer's problem (CAP) with
the bidders restricted to `T`, each bidder receiving at most one bundle, bundles pairwise
disjoint, and `V(T) = 0` when the auctioneer is not in `T`. Bidder `i : Fin n` is player `i.succ`. -/
noncomputable def capValue {n m : ℕ} (v : Fin n → Finset (Fin m) → ℝ) (T : Finset (Fin (n + 1))) :
    ℝ :=
  if (0 : Fin (n + 1)) ∈ T then
    sSup {w | ∃ y : Fin n → Option (Finset (Fin m)), (∀ i, i.succ ∉ T → y i = none)
      ∧ (∀ i j, i ≠ j → ∀ A B, y i = some A → y j = some B → Disjoint A B)
      ∧ w = ∑ i, (y i).elim 0 (v i)}
  else 0

/-- The core `C(S, V)` of the game restricted to the coalition `S`: payoff vectors whose total
on `S` is `V(S)` and which no sub-coalition can improve upon. -/
def InCore {n : ℕ} (V : Finset (Fin (n + 1)) → ℝ) (S : Finset (Fin (n + 1)))
    (π : Fin (n + 1) → ℝ) : Prop :=
  ∑ k ∈ S, π k = V S ∧ ∀ T ⊆ S, V T ≤ ∑ k ∈ T, π k

/-- (15.23)-(15.24): the VCG payoff vector `π̄(S)` of the game on `S`: bidder `k` receives
`V(S) − V(S ∖ k)` and the auctioneer the remainder. -/
def vcgPayoff {n : ℕ} (V : Finset (Fin (n + 1)) → ℝ) (S : Finset (Fin (n + 1))) (k : Fin (n + 1)) :
    ℝ :=
  if k = 0 then V S - ∑ l ∈ S.erase 0, (V S - V (S.erase l)) else V S - V (S.erase k)

/-- A payoff vector is bidder dominant on `S` if it lies in the core and gives every bidder at
least as much as every other core vector. -/
def BidderDominant {n : ℕ} (V : Finset (Fin (n + 1)) → ℝ) (S : Finset (Fin (n + 1)))
    (π : Fin (n + 1) → ℝ) : Prop :=
  InCore V S π ∧ ∀ π', InCore V S π' → ∀ k ∈ S, k ≠ 0 → π' k ≤ π k

/-- Bidder-submodularity: the marginal value of a bidder is weakly decreasing in the coalition. -/
def BidderSubmodular {n : ℕ} (V : Finset (Fin (n + 1)) → ℝ) : Prop :=
  ∀ k : Fin (n + 1), k ≠ 0 → ∀ S S' : Finset (Fin (n + 1)), (0 : Fin (n + 1)) ∈ S → S ⊆ S' →
    V (insert k S') - V S' ≤ V (insert k S) - V S
end SupplyChainTheory
