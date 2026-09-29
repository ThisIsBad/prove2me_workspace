import Mathlib

open Classical MeasureTheory

namespace FoundationsML.ModelSelection

/-- The empirical error of a hypothesis `h : X → Y` on a sample `S : Fin m → X` against a
target concept `c : X → Y` (Mohri, Rostamizadeh & Talwalkar, *Foundations of Machine
Learning*, 2nd ed., MIT Press 2018, Definition 2.2, p. 11, PDF p. 28, restated locally for
this chapter since drafts cannot import another chunk's draft module):
`R̂_S(h) = (1/m) ∑_{i=1}^m 1[h(x_i) ≠ c(x_i)]`. -/
noncomputable def EmpiricalError {X Y : Type*} {m : ℕ} (S : Fin m → X) (c h : X → Y) : ℝ :=
  ((Finset.univ.filter (fun i : Fin m => h (S i) ≠ c (S i))).card : ℝ) / (m : ℝ)

end FoundationsML.ModelSelection
