import Mathlib

namespace SimpsonInv.Vertex

/-- The extended service-time vector `(S₀, S₁, …, S_{n-1}, S_n)` of Simpson (1958), with `n = m + 1`
operations and `m` free variables. The Lean variable `S : Fin m → ℝ` stores the paper's `S_{j+1}` at
index `j`; `extVec S0 Sn S i` is the paper's `S_i` for every `i : ℕ`, with `S_i = S_n` for `i ≥ m + 1`. -/
def extVec {m : ℕ} (S0 Sn : ℝ) (S : Fin m → ℝ) (i : ℕ) : ℝ :=
  if h0 : i = 0 then S0 else if h : i ≤ m then S ⟨i - 1, by omega⟩ else Sn

/-- The `i`-th radicand `S_{i-1} - S_i + T_i` of equation (9) (used for `1 ≤ i ≤ m + 1`). -/
def radicand {m : ℕ} (T : ℕ → ℝ) (S0 Sn : ℝ) (S : Fin m → ℝ) (i : ℕ) : ℝ :=
  extVec S0 Sn S (i - 1) - extVec S0 Sn S i + T i

/-- The cost function of equation (9) and THEOREM I:
`f(S₁, …, S_{n-1}) = c + ∑_{i=1}^{n} r_i √(S_{i-1} - S_i + T_i)` with `n = m + 1`. -/
noncomputable def cost {m : ℕ} (c : ℝ) (r T : ℕ → ℝ) (S0 Sn : ℝ) (S : Fin m → ℝ) : ℝ :=
  c + ∑ i ∈ Finset.Icc 1 (m + 1), r i * Real.sqrt (radicand T S0 Sn S i)

/-- The domain `D` of THEOREM I: every variable `S_i` is nonnegative and every radicand
`S_{i-1} - S_i + T_i`, `1 ≤ i ≤ n`, is nonnegative. -/
def dom {m : ℕ} (T : ℕ → ℝ) (S0 Sn : ℝ) : Set (Fin m → ℝ) :=
  {S | (∀ j, 0 ≤ S j) ∧ ∀ i ∈ Finset.Icc 1 (m + 1), 0 ≤ radicand T S0 Sn S i}

/-- The number of the `2m + 1` defining inequalities of `D` that are tight (hold with equality) at `S`:
the number of variables `S_j = 0` plus the number of radicands equal to `0`. -/
noncomputable def tightCount {m : ℕ} (T : ℕ → ℝ) (S0 Sn : ℝ) (S : Fin m → ℝ) : ℕ :=
  by classical exact
    (Finset.univ.filter (fun j : Fin m => S j = 0)).card +
      ((Finset.Icc 1 (m + 1)).filter (fun i => radicand T S0 Sn S i = 0)).card

/-- The normal vectors of the defining inequalities of `D` that are tight at `S`.
For `S_j ≥ 0` the normal is `e_j`; for the `i`-th radicand it is
`e_{i-2} - e_{i-1}`, omitting coordinates outside `Fin m`. -/
def tightNormals {m : ℕ} (T : ℕ → ℝ) (S0 Sn : ℝ) (S : Fin m → ℝ) :
    Set (Fin m → ℝ) :=
  {v | ∃ j : Fin m, S j = 0 ∧ v = (fun k => if k = j then (1 : ℝ) else 0)} ∪
    {v | ∃ i ∈ Finset.Icc 1 (m + 1), radicand T S0 Sn S i = 0 ∧
      v = (fun k => (if k.val + 2 = i then (1 : ℝ) else 0) -
        (if k.val + 1 = i then (1 : ℝ) else 0))}

/-- The number of independent active boundary directions at `S`. In a full-dimensional
polyhedron, rank at least two means that `S` lies beyond the relative interior of a facet. -/
noncomputable def tightRank {m : ℕ} (T : ℕ → ℝ) (S0 Sn : ℝ) (S : Fin m → ℝ) : ℕ :=
  Module.finrank ℝ (Submodule.span ℝ (tightNormals T S0 Sn S))

/-- THEOREM II's processing times after tightly coupling operations `j` and `j + 1` (paper indices):
`T'_i = T_i` for `i < j`, `T'_j = T_j + T_{j+1}`, `T'_i = T_{i+1}` for `i > j`. -/
def coupledT (T : ℕ → ℝ) (j : ℕ) : ℕ → ℝ := fun i =>
  if i < j then T i else if i = j then T j + T (j + 1) else T (i + 1)

/-- THEOREM II's cost coefficients after eliminating inventory `I_j`:
`r'_i = r_i` for `i < j` and `r'_i = r_{i+1}` for `i ≥ j`. -/
def coupledR (r : ℕ → ℝ) (j : ℕ) : ℕ → ℝ := fun i =>
  if i < j then r i else r (i + 1)

/-- The correlated-demand cost of the *Extension of the main theorem* (p. 871): the square root of
equation (9) replaced by the power `t ↦ t ^ k`, i.e. `c + ∑_{i=1}^{n} r_i (S_{i-1} - S_i + T_i)^k`. -/
noncomputable def costPow {m : ℕ} (k c : ℝ) (r T : ℕ → ℝ) (S0 Sn : ℝ) (S : Fin m → ℝ) : ℝ :=
  c + ∑ i ∈ Finset.Icc 1 (m + 1), r i * (radicand T S0 Sn S i) ^ k

end SimpsonInv.Vertex
