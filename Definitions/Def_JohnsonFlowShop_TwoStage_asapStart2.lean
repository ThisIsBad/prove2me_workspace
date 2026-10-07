import Mathlib

namespace JohnsonFlowShop.TwoStage

/-- `asapC2 A B σ m` is the time at which machine 2 finishes the items in the first `m`
positions of the order `σ` under the as-soon-as-possible schedule (`0` for `m = 0`):
the item in position `m` starts on machine 2 at the later of its completion time on machine 1,
`∑_{l ≤ m} A (σ l)`, and the machine-2 completion of the previous position (`0` if `m = 0`). -/
def asapC2 {n : ℕ} (A B : Fin n → ℝ) (σ : Equiv.Perm (Fin n)) : ℕ → ℝ
  | 0 => 0
  | m + 1 =>
    if h : m < n then
      max (∑ l ∈ Finset.Iic (⟨m, h⟩ : Fin n), A (σ l)) (asapC2 A B σ m) + B (σ ⟨m, h⟩)
    else asapC2 A B σ m

/-- Machine-2 start times of the as-soon-as-possible schedule of the order `σ`: the item in
position `k = σ⁻¹ i` starts on machine 2 at the maximum of its completion time on machine 1,
`∑_{l ≤ k} A (σ l)`, and the machine-2 completion time of the item in the previous position. -/
def asapStart2 {n : ℕ} (A B : Fin n → ℝ) (σ : Equiv.Perm (Fin n)) (i : Fin n) : ℝ :=
  max (∑ l ∈ Finset.Iic (σ.symm i), A (σ l)) (asapC2 A B σ (σ.symm i).val)

end JohnsonFlowShop.TwoStage
