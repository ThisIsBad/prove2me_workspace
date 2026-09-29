import Mathlib
import Definitions.Def_MasekPaterson_Shared_editDist
import Definitions.Def_MasekPaterson_Shared_steps
import Definitions.Def_MasekPaterson_FourRussians_algorithms
open MasekPaterson.Shared

namespace MasekPaterson.FourRussians

/-- Correctness of the Masek–Paterson block algorithm with a string-independent finite table
(§2.2, Algorithm Z with Fetch = Algorithm Y). Over a finite alphabet, for a nonnegative
normalized cost function whose cost set `Ω` is discrete, there is one finite set `T` of
reals such that for every block size `m ≥ 1` and all strings `A, B` with `m ∣ |A|` and
`m ∣ |B|`: Algorithm Z returns `δ(γ, A, B)`, and every entry of every step vector
`P(i, j)` (`1 ≤ i ≤ |A|/m`, `0 ≤ j ≤ |B|/m`) and `Q(i, j)` (`0 ≤ i ≤ |A|/m`,
`1 ≤ j ≤ |B|/m`) that Algorithm Z computes lies in `T`. -/
theorem algZ_correct_finite_table {α : Type*} [Fintype α] (γ : EditOp α → ℝ)
    (hγ : ∀ o, 0 ≤ γ o) (hN : IsNormalized γ) (hΩ : IsDiscrete γ) :
    ∃ T : Finset ℝ, ∀ m : ℕ, 0 < m → ∀ A B : List α, m ∣ A.length → m ∣ B.length →
      algZ γ m A B = editDist γ A B ∧
      (∀ i j : ℕ, 1 ≤ i → i ≤ A.length / m → j ≤ B.length / m →
        ∀ k : Fin m, algZ_P γ m A B i j k ∈ T) ∧
      (∀ i j : ℕ, i ≤ A.length / m → 1 ≤ j → j ≤ B.length / m →
        ∀ k : Fin m, algZ_Q γ m A B i j k ∈ T) := by sorry

end MasekPaterson.FourRussians

