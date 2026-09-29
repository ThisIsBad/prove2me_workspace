import Mathlib

namespace FoundationsML.RademacherVC

/-- Theorem 3.7 (Massart's lemma; Mohri, Rostamizadeh & Talwalkar, *Foundations of Machine
Learning*, 2nd ed., MIT Press 2018, p. 35, PDF p. 52). Let `A ⊆ ℝ^m` be a finite (nonempty)
set, with `r = max_{x∈A} ‖x‖₂`. Then
`E_σ[(1/m) sup_{x∈A} ∑_{i=1}^m σ_i x_i] ≤ r sqrt(2 log|A|/m)`,
where `σ_1,…,σ_m` are independent uniform `{−1,+1}`-valued random variables and
`x_1,…,x_m` are the components of vector `x`.

**Formalization Note.** As in `EmpiricalRademacherComplexity`, `σ` ranges over `Fin m → Bool`
and the expectation over `σ` is the exact finite uniform average over its `2^m` outcomes;
`A.sup'` needs `A` nonempty, matching the book's own implicit assumption that `sup_{x∈A}` is
meaningful for a finite set `A`. -/
theorem massart_lemma
    {m : ℕ} (A : Finset (Fin m → ℝ)) (hA : A.Nonempty) (r : ℝ)
    (hr : ∀ x ∈ A, Real.sqrt (∑ i, (x i) ^ 2) ≤ r) :
    (1 / (2 : ℝ) ^ m) * ∑ σ : Fin m → Bool,
        (1 / (m : ℝ)) * A.sup' hA (fun x => ∑ i : Fin m, (if σ i then (1 : ℝ) else -1) * x i)
      ≤ r * Real.sqrt (2 * Real.log (A.card : ℝ) / m) := by sorry

end FoundationsML.RademacherVC
