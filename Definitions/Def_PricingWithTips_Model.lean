import Mathlib

open scoped BigOperators

namespace PricingWithTips

variable {B S D : Type*} [Fintype B] [Fintype S] [Fintype D]
  [DecidableEq B] [DecidableEq S] [DecidableEq D]

/-- A finite three-sided delivery market. Store production costs and product prices
are normalized to zero, as in Section 2 of the paper. -/
structure Market (B S D : Type*) where
  value : B → S → ℝ
  cost : D → B → S → ℝ
  value_nonneg : ∀ b s, 0 ≤ value b s
  cost_nonneg : ∀ d b s, 0 ≤ cost d b s

/-- A feasible three-sided allocation: each buyer receives at most one
store-courier pair, and no store or courier is used twice. -/
structure Allocation (B S D : Type*) where
  assigned : B → Option (S × D)
  store_unique : ∀ ⦃b₁ b₂ s d₁ d₂⦄,
    assigned b₁ = some (s, d₁) → assigned b₂ = some (s, d₂) → b₁ = b₂
  courier_unique : ∀ ⦃b₁ b₂ s₁ s₂ d⦄,
    assigned b₁ = some (s₁, d) → assigned b₂ = some (s₂, d) → b₁ = b₂

def Allocation.Trades (A : Allocation B S D) (b : B) (s : S) (d : D) : Prop :=
  A.assigned b = some (s, d)

def Allocation.Delivers (A : Allocation B S D) (b : B) (s : S) : Prop :=
  ∃ d, A.Trades b s d

def Allocation.Sells (A : Allocation B S D) (s : S) : Prop :=
  ∃ b d, A.Trades b s d

def Allocation.CourierWorks (A : Allocation B S D) (d : D) : Prop :=
  ∃ b s, A.Trades b s d

noncomputable def welfare (M : Market B S D) (A : Allocation B S D) : ℝ :=
  ∑ b, match A.assigned b with
    | none => 0
    | some (s, d) => M.value b s - M.cost d b s

def IsWelfareOptimal (M : Market B S D) (A : Allocation B S D) : Prop :=
  ∀ A' : Allocation B S D, welfare M A' ≤ welfare M A

def counterfactualTip (t : B → S → ℝ) (b : B) (s : S) (τ : ℝ)
    (b' : B) (s' : S) : ℝ :=
  if b' = b then if s' = s then τ else 0 else t b' s'

/-- Courier `d` would weakly prefer order `(b,s)` to idling and to every
other order if buyer `b` offered counterfactual tip `τ`, while her tips at
other stores are zero and all other buyers' tips stay fixed. -/
def CourierAccepts (M : Market B S D) (w t : B → S → ℝ)
    (b : B) (s : S) (τ : ℝ) (d : D) : Prop :=
  0 ≤ w b s + τ - M.cost d b s ∧
  ∀ b' s',
    w b' s' + counterfactualTip t b s τ b' s' - M.cost d b' s' ≤
      w b s + τ - M.cost d b s

/-- Definition 2.2's minimum tip: the infimum of nonnegative tips that make
at least one courier willing to deliver the selected order. -/
noncomputable def minimumTip (M : Market B S D) (w t : B → S → ℝ)
    (b : B) (s : S) : ℝ :=
  sInf {τ : ℝ | 0 ≤ τ ∧ ∃ d, CourierAccepts M w t b s τ d}

/-- Appendix A's closed-form expression for the minimum tip. -/
noncomputable def minimumTipFormula (M : Market B S D) (w t : B → S → ℝ)
    (b : B) (s : S) : ℝ :=
  ⨅ d, max 0 (max (M.cost d b s - w b s)
    (⨆ (b' : B) (s' : S), if (b', s') = (b, s) then 0 else
      w b' s' + (if b' = b then 0 else t b' s') - M.cost d b' s' - w b s + M.cost d b s))

def courierUtility (M : Market B S D) (w t : B → S → ℝ)
    (d : D) (b : B) (s : S) : ℝ :=
  w b s + t b s - M.cost d b s

def IsWithoutTipEquilibrium (M : Market B S D) (A : Allocation B S D)
    (p : S → ℝ) (w : B → S → ℝ) : Prop :=
  (∀ s, 0 ≤ p s) ∧ (∀ b s, 0 ≤ w b s) ∧
  (∀ b,
    match A.assigned b with
    | none => ∀ s, M.value b s - p s ≤ 0
    | some (s, _) =>
        0 ≤ M.value b s - p s ∧
        ∀ s', M.value b s' - p s' ≤ M.value b s - p s) ∧
  (∀ d b s, A.Trades b s d →
    0 ≤ w b s - M.cost d b s ∧
    ∀ b' s', w b' s' - M.cost d b' s' ≤ w b s - M.cost d b s) ∧
  (∀ d, ¬ A.CourierWorks d → ∀ b s, w b s - M.cost d b s ≤ 0) ∧
  (∀ s, ¬ A.Sells s → p s = 0) ∧
  (∀ b s, ¬ A.Delivers b s → w b s = 0)

def IsWithTipEquilibrium (M : Market B S D) (A : Allocation B S D)
    (p : S → ℝ) (w t : B → S → ℝ) : Prop :=
  (∀ s, 0 ≤ p s) ∧ (∀ b s, 0 ≤ w b s) ∧ (∀ b s, 0 ≤ t b s) ∧
  (∀ b,
    match A.assigned b with
    | none => ∀ s, M.value b s - p s - minimumTip M w t b s ≤ 0
    | some (s, _) =>
        t b s = minimumTip M w t b s ∧
        0 ≤ M.value b s - p s - minimumTip M w t b s ∧
        ∀ s', M.value b s' - p s' - minimumTip M w t b s' ≤
          M.value b s - p s - minimumTip M w t b s) ∧
  (∀ d b s, A.Trades b s d →
    0 ≤ courierUtility M w t d b s ∧
    ∀ b' s', courierUtility M w t d b' s' ≤ courierUtility M w t d b s) ∧
  (∀ d, ¬ A.CourierWorks d → ∀ b s, courierUtility M w t d b s ≤ 0) ∧
  (∀ s, ¬ A.Sells s → p s = 0) ∧
  (∀ b s, ¬ A.Delivers b s → w b s = 0 ∧ t b s = 0)

def HasWithTipEquilibriumAt (M : Market B S D) (A : Allocation B S D) : Prop :=
  ∃ p w t, IsWithTipEquilibrium M A p w t

def IsCourierPlanFor (M : Market B S D) (A : Allocation B S D)
    (w : B → S → ℝ) : Prop :=
  (∀ b s, 0 ≤ w b s) ∧
  (∀ d b s, A.Trades b s d →
    0 ≤ w b s - M.cost d b s ∧
    ∀ b' s', w b' s' - M.cost d b' s' ≤ w b s - M.cost d b s) ∧
  (∀ d, ¬ A.CourierWorks d → ∀ b s, w b s - M.cost d b s ≤ 0) ∧
  (∀ b s, ¬ A.Delivers b s → w b s = 0)

noncomputable def courierRealizedUtility (M : Market B S D) (A : Allocation B S D)
    (w : B → S → ℝ) (d : D) : ℝ := by
  classical
  exact if h : ∃ b s, A.Trades b s d then
      let b := Classical.choose h
      let hs := Classical.choose_spec h
      let s := Classical.choose hs
      w b s - M.cost d b s
    else 0

def IsMaximalCourierUtility (M : Market B S D) (A : Allocation B S D)
    (uBar : D → ℝ) : Prop :=
  (∃ w, IsCourierPlanFor M A w ∧ ∀ d, courierRealizedUtility M A w d = uBar d) ∧
  ∀ w, IsCourierPlanFor M A w → ∀ d, courierRealizedUtility M A w d ≤ uBar d

noncomputable def requiredTip (M : Market B S D) (A : Allocation B S D)
    (uBar : D → ℝ) (b : B) (s : S) : ℝ := by
  classical
  exact if A.Delivers b s then 0 else ⨅ d, M.cost d b s + uBar d

noncomputable def adjustedValue (M : Market B S D) (A : Allocation B S D)
    (uBar : D → ℝ) (b : B) (s : S) : ℝ :=
  M.value b s - requiredTip M A uBar b s

structure BuyerMatching (B S : Type*) where
  assigned : B → Option S
  store_unique : ∀ ⦃b₁ b₂ s⦄, assigned b₁ = some s → assigned b₂ = some s → b₁ = b₂

def Allocation.toBuyerMatching (A : Allocation B S D) : BuyerMatching B S where
  assigned := fun b => (A.assigned b).map Prod.fst
  store_unique := by
    intro b₁ b₂ s h₁ h₂
    simp only [Option.map_eq_some_iff] at h₁ h₂
    obtain ⟨x₁, hx₁, rfl⟩ := h₁
    obtain ⟨x₂, hx₂, hfst⟩ := h₂
    cases x₁ with
    | mk s₁ d₁ =>
      cases x₂ with
      | mk s₂ d₂ =>
        simp only at hfst
        subst s₂
        exact A.store_unique hx₁ hx₂

noncomputable def matchingWeight (z : BuyerMatching B S) (q : B → S → ℝ) : ℝ :=
  ∑ b, match z.assigned b with | none => 0 | some s => q b s

def IsMaximumWeight (z : BuyerMatching B S) (q : B → S → ℝ) : Prop :=
  ∀ z' : BuyerMatching B S, matchingWeight z' q ≤ matchingWeight z q

def CourierStoreDecomposable (M : Market B S D) : Prop :=
  ∃ cBS : B → S → ℝ, ∃ cDS : D → S → ℝ,
    ∀ d b s, M.cost d b s = cBS b s + cDS d s

def CourierBuyerDecomposable (M : Market B S D) : Prop :=
  ∃ cBS : B → S → ℝ, ∃ cDB : D → B → ℝ,
    ∀ d b s, M.cost d b s = cBS b s + cDB d b

/-- A non-vacuous formulation of the paper's “arbitrarily low” clause:
for every loss threshold there is a finite structured market with at least one
without-tip equilibrium, positive optimal welfare, and every such equilibrium
has welfare at most the negative threshold. -/
def ArbitrarilyLowWithoutTipWelfare : Prop :=
  ∀ K : ℝ, 0 < K →
    ∃ M : Market (Fin 2) (Fin 1) (Fin 2),
      (CourierStoreDecomposable M ∨ CourierBuyerDecomposable M) ∧
      (∃ A : Allocation (Fin 2) (Fin 1) (Fin 2),
        IsWelfareOptimal M A ∧ 0 < welfare M A) ∧
      (∃ A p w, IsWithoutTipEquilibrium M A p w) ∧
      ∀ A p w, IsWithoutTipEquilibrium M A p w → welfare M A ≤ -K

end PricingWithTips
