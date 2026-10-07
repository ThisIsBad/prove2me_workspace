import Mathlib
import Definitions.Def_CuttingStock63_Knapsack_Problem

namespace CuttingStock63.Knapsack

/-! The Knapsack Method of Gilmore & Gomory (1963), Steps (2)–(7), pp. 867–868, as a
transition system. Step (1) (sorting by density and by stock length) is not a step: its output
is a hypothesis of the theorems about this system. Stock lengths are indexed by `Fin k`
(j = 1 of the paper is index 0). -/

/-- Steps (2) and (7): keep the coefficients of `a` with index `< s` and set, in increasing order
of `i ≥ s`, a_i := [(cap − used)/l_i], where `used` is the length of the coefficients already
fixed. Step (2) is `greedyFill l L_1 0 0`; Step (7) is `greedyFill l L_t a s`. -/
noncomputable def greedyFill {m : ℕ} (l : Fin m → ℝ) (cap : ℝ) (a : Fin m → ℕ) (s : ℕ) :
    Fin m → ℕ :=
  ((List.finRange m).foldl
    (fun (acc : (Fin m → ℕ) × ℝ) (i : Fin m) =>
      if i.val < s then acc
      else
        let q : ℕ := ⌊(cap - acc.2) / l i⌋₊
        (Function.update acc.1 i q, acc.2 + l i * (q : ℝ)))
    (a, lam l a s)).1

/-- The step of the method that is executed next: Step (3) `update`, Step (4) `backtrack`,
Step (5) `test` (with Step (7) folded into its successful branch), Step (6) `step6`, and the
end of the method `done`. -/
inductive Phase
  | update
  | backtrack
  | test
  | step6
  | done
  deriving DecidableEq

/-- A state of the method: the current vector `a`, the level `s` (1-based, as in the paper),
the index `t`, the current best values `M j`, and the step to execute next. -/
structure State (m k : ℕ) where
  a : Fin m → ℕ
  s : ℕ
  t : Fin k
  M : Fin k → ℝ
  phase : Phase

/-- Step (2): a_1 = [L_1/l_1], a_2 = [(L_1 − l_1 a_1)/l_2], …; t = 1 and M_j = c_j; then go to
Step (3). (The level `s` is not used before Step (4) sets it.) -/
noncomputable def start {m k : ℕ} (l : Fin m → ℝ) (L c : Fin k → ℝ) (hk : 0 < k) : State m k :=
  { a := greedyFill l (L ⟨0, hk⟩) 0 0, s := 0, t := ⟨0, hk⟩, M := c, phase := .update }

/-- The test of Step (5) for the stock length `j`, applied to the (already decremented) prefix
(α)_s: L_j ≥ λ·(α)_s and (L_j − λ·(α)_s) b_{s+1} > (M_j − β·(α)_s) l_{s+1}. -/
def TestHolds {m k : ℕ} (l b : Fin m → ℝ) (L M : Fin k → ℝ) (a : Fin m → ℕ) (s : ℕ)
    (j : Fin k) : Prop :=
  lam l a s ≤ L j ∧ (L j - lam l a s) * nextB b s > (M j - bet b a s) * nextL l s

/-- One move of the method. "The smallest j" and "the largest i" are relational premises. -/
inductive Step {m k : ℕ} (l b : Fin m → ℝ) (L c : Fin k → ℝ) : State m k → State m k → Prop
  /-- Step (3): for those j, t ≤ j ≤ k, with L_j ≥ λ·(α)_m and β·(α)_m > M_j, redefine M_j to be
  β·(α)_m; then go to Step (4). -/
  | update (a : Fin m → ℕ) (s : ℕ) (t : Fin k) (M : Fin k → ℝ) :
      Step l b L c ⟨a, s, t, M, .update⟩
        ⟨a, s, t, fun j => if t ≤ j ∧ Fits l (L j) a ∧ M j < bet b a m then bet b a m else M j,
          .backtrack⟩
  /-- Step (4): let s be the largest i with a_i ≠ 0; go to Step (5). -/
  | backtrack_found (a : Fin m → ℕ) (s : ℕ) (t : Fin k) (M : Fin k → ℝ) (i : Fin m)
      (hi : a i ≠ 0) (hmax : ∀ i' : Fin m, i < i' → a i' = 0) :
      Step l b L c ⟨a, s, t, M, .backtrack⟩ ⟨a, i.val + 1, t, M, .test⟩
  /-- Step (4) when every coefficient is 0: nothing lies below the zero vector, so the method
  stops (a case the page does not mention). -/
  | backtrack_zero (a : Fin m → ℕ) (s : ℕ) (t : Fin k) (M : Fin k → ℝ)
      (h0 : ∀ i : Fin m, a i = 0) :
      Step l b L c ⟨a, s, t, M, .backtrack⟩ ⟨a, s, t, M, .done⟩
  /-- Steps (5) and (7): redefine a_s to be a_s − 1; let t be the smallest j for which the test
  holds; compute a_{s+1}, …, a_m greedily for L_t; go to Step (3). -/
  | test_pass (a : Fin m → ℕ) (s : ℕ) (t : Fin k) (M : Fin k → ℝ) (hs : 0 < s) (hsm : s ≤ m)
      (t' : Fin k) (ht' : TestHolds l b L M (decrAt a s) s t')
      (hmin : ∀ j : Fin k, TestHolds l b L M (decrAt a s) s j → t' ≤ j) :
      Step l b L c ⟨a, s, t, M, .test⟩ ⟨greedyFill l (L t') (decrAt a s) s, s, t', M, .update⟩
  /-- Step (5) when the test holds for no j: redefine a_s to be a_s − 1 and go to Step (6). -/
  | test_fail (a : Fin m → ℕ) (s : ℕ) (t : Fin k) (M : Fin k → ℝ) (hs : 0 < s) (hsm : s ≤ m)
      (hnone : ∀ j : Fin k, ¬ TestHolds l b L M (decrAt a s) s j) :
      Step l b L c ⟨a, s, t, M, .test⟩ ⟨decrAt a s, s, t, M, .step6⟩
  /-- Step (6): redefine s to be the largest i, 1 ≤ i ≤ s − 1, with a_i ≠ 0; go to Step (5). -/
  | step6_found (a : Fin m → ℕ) (s : ℕ) (t : Fin k) (M : Fin k → ℝ) (i : Fin m)
      (hi : i.val + 1 ≤ s - 1) (hai : a i ≠ 0)
      (hmax : ∀ i' : Fin m, i < i' → i'.val + 1 ≤ s - 1 → a i' = 0) :
      Step l b L c ⟨a, s, t, M, .step6⟩ ⟨a, i.val + 1, t, M, .test⟩
  /-- Step (6) when there is no such i: the current M_j are the maximums to be found. -/
  | step6_none (a : Fin m → ℕ) (s : ℕ) (t : Fin k) (M : Fin k → ℝ)
      (hnone : ∀ i : Fin m, i.val + 1 ≤ s - 1 → a i = 0) :
      Step l b L c ⟨a, s, t, M, .step6⟩ ⟨a, s, t, M, .done⟩

/-- A state is reachable if some run of the method from Step (2) arrives at it. -/
def Reachable {m k : ℕ} (l b : Fin m → ℝ) (L c : Fin k → ℝ) (hk : 0 < k) (σ : State m k) :
    Prop :=
  Relation.ReflTransGen (Step l b L c) (start l L c hk) σ

end CuttingStock63.Knapsack
