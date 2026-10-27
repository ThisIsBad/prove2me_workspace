import Mathlib

namespace HetExponomial.ChoiceProb

open MeasureTheory ProbabilityTheory

variable {n : ℕ}

/-- Joint law of the independent errors `z_j ~ Exp(λ_j)`, `j ∈ N = Fin n` (p. 4):
the product of the exponential laws `expMeasure (lam j)`. -/
noncomputable def errorLaw (lam : Fin n → ℝ) : Measure (Fin n → ℝ) :=
  Measure.pi (fun j => expMeasure (lam j))

/-- The choice probability `Q_i(u, λ) = P{u_i − z_i ≥ u_j − z_j ∀ j ∈ N, j ≠ i}`,
the first line of (1), p. 6. -/
noncomputable def choiceProb (u lam : Fin n → ℝ) (i : Fin n) : ℝ :=
  (errorLaw lam {z | ∀ j, j ≠ i → u j - z j ≤ u i - z i}).toReal

/-- The paper's pdf `f_i(z) = λ_i e^{−λ_i z}` for `z ≥ 0`, `0` for `z < 0` (p. 4). -/
noncomputable def pdfExp (r z : ℝ) : ℝ := if 0 ≤ z then r * Real.exp (-(r * z)) else 0

/-- The paper's cdf `F_i(z) = 1 − e^{−λ_i z}` for `z ≥ 0`, `0` for `z < 0` (p. 4). -/
noncomputable def cdfExp (r z : ℝ) : ℝ := if 0 ≤ z then 1 - Real.exp (-(r * z)) else 0

/-- `B(x) = {j ∈ N : u_j ≥ x}` (proof of Theorem 1, p. 43). -/
noncomputable def betterThan (u : Fin n → ℝ) (x : ℝ) : Finset (Fin n) :=
  Finset.univ.filter (fun j => x ≤ u j)

/-- `B_i = {j ∈ N : u_j ≥ u_i}` (p. 6). -/
noncomputable def better (u : Fin n → ℝ) (i : Fin n) : Finset (Fin n) :=
  betterThan u (u i)

/-- `B_i^+ = {j ∈ N : u_j > u_i}` (p. 6). -/
noncomputable def strictlyBetter (u : Fin n → ℝ) (i : Fin n) : Finset (Fin n) :=
  Finset.univ.filter (fun j => u i < u j)

/-- `W_i^− = {j ∈ N : u_j < u_i}` (p. 6). -/
noncomputable def strictlyWorse (u : Fin n → ℝ) (i : Fin n) : Finset (Fin n) :=
  Finset.univ.filter (fun j => u j < u i)

/-- `L_i = ∑_{j ∈ B_i} λ_j` (p. 6). -/
noncomputable def Lsum (u lam : Fin n → ℝ) (i : Fin n) : ℝ :=
  ∑ j ∈ better u i, lam j

/-- `L_i^+ = ∑_{j ∈ B_i^+} λ_j` (p. 6). The paper defines it only for `u_i < u_max`; here it
is total and equals `0` at a choice of maximal ideal utility. -/
noncomputable def Lplus (u lam : Fin n → ℝ) (i : Fin n) : ℝ :=
  ∑ j ∈ strictlyBetter u i, lam j

/-- `G_i(u, λ) = (λ_i / L_i) · exp[−∑_{j ∈ B_i} λ_j (u_j − u_i)]`, equation (2), p. 6. -/
noncomputable def G (u lam : Fin n → ℝ) (i : Fin n) : ℝ :=
  lam i / Lsum u lam i * Real.exp (-(∑ j ∈ better u i, lam j * (u j - u i)))

/-- The set of distinct ideal utilities `{a_1, …, a_l}` (proof of Theorem 1, p. 43). -/
noncomputable def levels (u : Fin n → ℝ) : Finset ℝ :=
  Finset.univ.image u

/-- The distinct ideal utilities in increasing order, `a_1 < a_2 < ⋯ < a_l`
(proof of Theorem 1, p. 43), indexed from `0`: the paper's `a_w` is `level u ⟨w - 1, _⟩`. -/
noncomputable def level (u : Fin n → ℝ) : Fin (levels u).card ↪o ℝ :=
  (levels u).orderEmbOfFin rfl

/-- The tail integral `∫_c^∞ exp[−∑_{j ∈ B(x)} λ_j (u_j − u_i + z)] dz` appearing in (16),
p. 43. -/
noncomputable def tailInt (u lam : Fin n → ℝ) (i : Fin n) (x c : ℝ) : ℝ :=
  ∫ z in Set.Ioi c, Real.exp (-(∑ j ∈ betterThan u x, lam j * (u j - u i + z)))

end HetExponomial.ChoiceProb
