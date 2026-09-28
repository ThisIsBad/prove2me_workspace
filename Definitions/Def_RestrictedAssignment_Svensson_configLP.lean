import Mathlib

namespace RestrictedAssignment.Svensson

open Finset

variable {J M : Type} [Fintype J] [Fintype M] [DecidableEq J] [DecidableEq M]

/-- Svensson, arXiv:1011.1168v2, p. 3, Sect. 2: `C(i, T)`, the configurations for machine `i`
with respect to the target makespan `T`: the sets of jobs `C ⊆ J` with `C ⊆ {j : i ∈ Γ(j)}` and
`p(C) = ∑_{j ∈ C} p_j ≤ T`. -/
noncomputable def configs (Γ : J → Finset M) (p : J → ℝ) (T : ℝ) (i : M) : Finset (Finset J) :=
  (Finset.univ : Finset (Finset J)).filter (fun C => (∀ j ∈ C, i ∈ Γ j) ∧ ∑ j ∈ C, p j ≤ T)

/-- Svensson, arXiv:1011.1168v2, p. 3, [C-LP]: the configuration LP for target makespan `T` is
feasible, i.e. there are `x_{i,C} ≥ 0` with `∑_{C ∈ C(i,T)} x_{i,C} ≤ 1` for every machine `i`
and `∑_i ∑_{C ∈ C(i,T), C ∋ j} x_{i,C} ≥ 1` for every job `j`. (Values of `x` at sets that are
not configurations of `i` occur in no constraint.) -/
def CLPFeasible (Γ : J → Finset M) (p : J → ℝ) (T : ℝ) : Prop :=
  ∃ x : M → Finset J → ℝ,
    (∀ i C, 0 ≤ x i C) ∧
    (∀ i, ∑ C ∈ configs Γ p T i, x i C ≤ 1) ∧
    (∀ j, 1 ≤ ∑ i, ∑ C ∈ (configs Γ p T i).filter (fun C => j ∈ C), x i C)

/-- Svensson, arXiv:1011.1168v2, p. 4, Dual of [C-LP]: `(y, z)` is a feasible solution of the
dual, i.e. `y, z ≥ 0` and `y_i ≥ ∑_{j ∈ C} z_j` for every machine `i` and every `C ∈ C(i, T)`. -/
def CLPDualFeasible (Γ : J → Finset M) (p : J → ℝ) (T : ℝ) (y : M → ℝ) (z : J → ℝ) : Prop :=
  (∀ i, 0 ≤ y i) ∧ (∀ j, 0 ≤ z j) ∧ ∀ i, ∀ C ∈ configs Γ p T i, ∑ j ∈ C, z j ≤ y i

/-- Svensson, arXiv:1011.1168v2, p. 1: the load `∑_{j ∈ σ⁻¹(i)} p_j` of machine `i` under a
schedule `σ : J → M`; the makespan of `σ` is the maximum load. -/
def schedLoad (p : J → ℝ) (σ : J → M) (i : M) : ℝ :=
  ∑ j ∈ Finset.univ.filter (fun j => σ j = i), p j

end RestrictedAssignment.Svensson
