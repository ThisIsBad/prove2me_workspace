import Mathlib

namespace JohnsonFlowShop.ThreeStage

/-- `asapDone A B C σ m` is the triple of times at which machines 1, 2 and 3 finish the items in
the first `m` positions of the order `σ` (`σ k` = item in position `k`, positions `0` to `n`
minus one) under the as-soon-as-possible schedule; it is `(0, 0, 0)` for `m = 0`. With
`i = σ m` the item in position `m` and `(c₁, c₂, c₃)` the times after `m` positions:
`c₁' = c₁ + A i`, `c₂' = max c₂ c₁' + B i`, `c₃' = max c₃ c₂' + C i`. -/
def asapDone {n : ℕ} (A B C : Fin n → ℝ) (σ : Equiv.Perm (Fin n)) : ℕ → ℝ × ℝ × ℝ
  | 0 => (0, 0, 0)
  | m + 1 =>
    if h : m < n then
      let c := asapDone A B C σ m
      let i := σ ⟨m, h⟩
      let d₁ := c.1 + A i
      let d₂ := max c.2.1 d₁ + B i
      (d₁, d₂, max c.2.2 d₂ + C i)
    else asapDone A B C σ m

/-- Machine 1 start time of item `i` in the as-soon-as-possible schedule of `σ`: the time at
which machine 1 finishes the items placed before `i` (there are no delays on machine 1). -/
def asapStart1 {n : ℕ} (A B C : Fin n → ℝ) (σ : Equiv.Perm (Fin n)) (i : Fin n) : ℝ :=
  (asapDone A B C σ (σ.symm i).val).1

/-- Machine 2 start time of item `i` in the as-soon-as-possible schedule of `σ`: the later of
its machine 1 completion time and the time machine 2 finishes the items placed before `i`. -/
def asapStart2 {n : ℕ} (A B C : Fin n → ℝ) (σ : Equiv.Perm (Fin n)) (i : Fin n) : ℝ :=
  max (asapDone A B C σ (σ.symm i).val).2.1 (asapStart1 A B C σ i + A i)

/-- Machine 3 start time of item `i` in the as-soon-as-possible schedule of `σ`: the later of
its machine 2 completion time and the time machine 3 finishes the items placed before `i`. -/
def asapStart3 {n : ℕ} (A B C : Fin n → ℝ) (σ : Equiv.Perm (Fin n)) (i : Fin n) : ℝ :=
  max (asapDone A B C σ (σ.symm i).val).2.2 (asapStart2 A B C σ i + B i)

end JohnsonFlowShop.ThreeStage
