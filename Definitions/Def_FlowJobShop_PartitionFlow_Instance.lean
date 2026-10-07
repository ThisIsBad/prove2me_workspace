import Mathlib
import Definitions.Def_FlowJobShop_PartitionFlow_FlowShop

namespace FlowJobShop.PartitionFlow

/-- `T = ∑_{i=1}^n a_i`, as a real number. -/
noncomputable def T {n : ℕ} (a : Fin n → ℕ) : ℝ := ∑ i, (a i : ℝ)

/-- The task times of the flow shop FS of the proof of Lemma 1 (Gonzalez–Sahni 1978, p. 39).
Jobs are `Fin n ⊕ Fin 2`: `Sum.inl i` is job `i + 1` (`1 ≤ i + 1 ≤ n`), `Sum.inr 0` is job
`n + 1` and `Sum.inr 1` is job `n + 2`. Processors `0, 1, 2` are `P_1, P_2, P_3`.
* job `i ≤ n`: `t_{1,i} = a_i`, `t_{2,i} = 0`, `t_{3,i} = a_i`;
* job `n + 1`: `t_{1,n+1} = T/2`, `t_{2,n+1} = T`, `t_{3,n+1} = 0`;
* job `n + 2`: `t_{1,n+2} = 0`, `t_{2,n+2} = T`, `t_{3,n+2} = T/2`. -/
noncomputable def fsTimes {n : ℕ} (a : Fin n → ℕ) : Fin 3 → Fin n ⊕ Fin 2 → ℝ
  | j, Sum.inl i => ![(a i : ℝ), 0, (a i : ℝ)] j
  | j, Sum.inr 0 => ![T a / 2, T a, 0] j
  | j, Sum.inr 1 => ![0, T a, T a / 2] j

theorem T_nonneg {n : ℕ} (a : Fin n → ℕ) : 0 ≤ T a :=
  Finset.sum_nonneg (fun i _ => Nat.cast_nonneg (a i))

theorem fsTimes_nonneg {n : ℕ} (a : Fin n → ℕ) (j : Fin 3) (i : Fin n ⊕ Fin 2) :
    0 ≤ fsTimes a j i := by
  have hT := T_nonneg a
  rcases i with i | k
  · fin_cases j <;> simp [fsTimes]
  · fin_cases k <;> fin_cases j <;> simp [fsTimes] <;> linarith

/-- The three-processor flow shop **FS** built from the PARTITION instance `a` in the proof of
Lemma 1 (p. 39), with `n + 2` jobs and the task times `fsTimes a`. -/
noncomputable def FS {n : ℕ} (a : Fin n → ℕ) : FlowShop 3 (Fin n ⊕ Fin 2) :=
  ⟨fsTimes a, fsTimes_nonneg a, by decide⟩

end FlowJobShop.PartitionFlow
