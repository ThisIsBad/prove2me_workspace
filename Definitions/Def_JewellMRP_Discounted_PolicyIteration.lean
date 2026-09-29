import Mathlib
import Definitions.Def_JewellMRP_Discounted_MRP

namespace JewellMRP.Discounted

variable {S A : Type*} [Fintype S]

/-- The `n`-step discounted return of a (possibly nonstationary) policy `π`, with boundary
rewards `V0` (the `V_i(0, α)` of p. 942). `π k i` is the alternative used in state `i` at the
`k`-th transition (`k = 0, 1, 2, …`, counted from the start). A stationary policy `d : S → A`
is the constant sequence `fun _ => d`. -/
noncomputable def policyReturn (M : MRP S A) (α : ℝ) :
    (ℕ → S → A) → (S → ℝ) → ℕ → S → ℝ
  | _, V0, 0 => V0
  | π, V0, n + 1 => fun i =>
      test M α (π 0 i) i (policyReturn M α (fun k => π (k + 1)) V0 n)

/-- The optimal `n`-step discounted returns `V_i(n, α)` of the recurrence (6), with boundary
rewards `V_i(0, α) = V0 i`. -/
noncomputable def optValue [Fintype A] [Nonempty A] (M : MRP S A) (α : ℝ) (V0 : S → ℝ) :
    ℕ → S → ℝ
  | 0 => V0
  | n + 1 => maxTest M α (optValue M α V0 n)

/-- The value-determination equations (15) of the stationary policy `d`:
`v_i = ρ^{d(i)}_i(α) + Σ_j p^{d(i)}_{ij} f̃^{d(i)}_{ij}(α) v_j` for every state `i`. -/
def SolvesEval (M : MRP S A) (α : ℝ) (d : S → A) (v : S → ℝ) : Prop :=
  ∀ i, v i = test M α (d i) i v

/-- The policy-improvement step of Fig. 1: in every state `i`, the new alternative `d' i`
maximizes the test quantity computed with the present returns `v`; and if the old alternative
`d i` already attains that maximum (no improvement in the test quantity), it is retained. -/
def IsImprovement [Fintype A] [Nonempty A] (M : MRP S A) (α : ℝ) (d : S → A) (v : S → ℝ)
    (d' : S → A) : Prop :=
  ∀ i, test M α (d' i) i v = maxTest M α v i ∧
    (test M α (d i) i v = maxTest M α v i → d' i = d i)

/-- A run of the algorithm of Fig. 1: `d k` is the policy of cycle `k`, `v k` solves the
value-determination equations (15) for it, and `d (k + 1)` is obtained from `d k` and `v k` by
the policy-improvement step. -/
def IsFig1Run [Fintype A] [Nonempty A] (M : MRP S A) (α : ℝ) (d : ℕ → S → A)
    (v : ℕ → S → ℝ) : Prop :=
  ∀ k, SolvesEval M α (d k) (v k) ∧ IsImprovement M α (d k) (v k) (d (k + 1))

end JewellMRP.Discounted
