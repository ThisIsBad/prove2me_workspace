import Mathlib
import Definitions.Def_MulticutLShaped_SimpleRecourse_Model

namespace MulticutLShaped.SimpleRecourse

variable {n1 m1 m2 J : ℕ}

/-- The cut row `E_l = p_ij q_ij T_i` of Step 2 (p. 389), for the pair `l = (i, j)`;
`T_i` is row `i` of `T`. -/
def cutE (inst : Instance n1 m1 m2 J) (l : Fin m2 × Fin J) : Fin n1 → ℝ :=
  (inst.p l.1 l.2 * inst.q l.1 l.2) • inst.T l.1

/-- The cut right-hand side `e_l = p_ij q_ij h_ij` of Step 2 (p. 389), for `l = (i, j)`. -/
def cute (inst : Instance n1 m1 m2 J) (l : Fin m2 × Fin J) : ℝ :=
  inst.p l.1 l.2 * inst.q l.1 l.2 * inst.h l.1 l.2

/-- Feasibility for the master LP (26) when the set of pairs identified so far in Step 2 is `I`:
`Ax = b`, `x ≥ 0` (from (3); omitted in the display of (26)), and `u_l ≥ e_l − E_l x`, `u_l ≥ 0`
for every `l ∈ I`. The values of `u` outside `I` are not constrained and do not enter (26). -/
def MasterFeasible (inst : Instance n1 m1 m2 J) (I : Finset (Fin m2 × Fin J))
    (x : Fin n1 → ℝ) (u : Fin m2 × Fin J → ℝ) : Prop :=
  inst.A.mulVec x = inst.b ∧ (∀ k, 0 ≤ x k) ∧
    ∀ l ∈ I, cute inst l - cutE inst l ⬝ᵥ x ≤ u l ∧ 0 ≤ u l

/-- The objective of the master LP (26): `cx + Σ_i Σ_j p_ij q⁻_ij (T_i x) + Σ_{l ∈ I} u_l`. -/
def masterObj (inst : Instance n1 m1 m2 J) (I : Finset (Fin m2 × Fin J))
    (x : Fin n1 → ℝ) (u : Fin m2 × Fin J → ℝ) : ℝ :=
  inst.c ⬝ᵥ x + ∑ i, ∑ j, inst.p i j * inst.qminus i j * (inst.T i ⬝ᵥ x) + ∑ l ∈ I, u l

/-- `(x, u)` is an optimal solution of the master LP (26) with identified pairs `I` (Step 1). -/
def MasterOptimal (inst : Instance n1 m1 m2 J) (I : Finset (Fin m2 × Fin J))
    (x : Fin n1 → ℝ) (u : Fin m2 × Fin J → ℝ) : Prop :=
  MasterFeasible inst I x u ∧
    ∀ x' u', MasterFeasible inst I x' u' → masterObj inst I x u ≤ masterObj inst I x' u'

open Classical in
/-- The pairs `(i, j)` not yet identified (`∉ I`) for which the constraint (27),
`0 ≥ p_ij q_ij (h_ij − T_i x)`, is violated at `x` (Step 2, p. 389). -/
noncomputable def violated (inst : Instance n1 m1 m2 J) (I : Finset (Fin m2 × Fin J))
    (x : Fin n1 → ℝ) : Finset (Fin m2 × Fin J) :=
  Finset.univ.filter fun l =>
    l ∉ I ∧ 0 < inst.p l.1 l.2 * inst.q l.1 l.2 * (inst.h l.1 l.2 - inst.T l.1 ⬝ᵥ x)

/-- One pass Step 1 → Step 2 → Step 1 of the multicut algorithm for simple recourse problems:
some optimal solution `(x, u)` of (26) with identified pairs `I` violates (27) for at least one
unidentified pair, and every such pair is added: `I' = I ∪ violated I x`. -/
def Step (inst : Instance n1 m1 m2 J) (I I' : Finset (Fin m2 × Fin J)) : Prop :=
  ∃ x u, MasterOptimal inst I x u ∧ (violated inst I x).Nonempty ∧ I' = I ∪ violated inst I x

/-- The algorithm stops at `x` with identified pairs `I`: `(x, u)` is optimal for (26) for some
`u`, and (27) is violated for no unidentified pair. -/
def StopsAt (inst : Instance n1 m1 m2 J) (I : Finset (Fin m2 × Fin J)) (x : Fin n1 → ℝ) : Prop :=
  ∃ u, MasterOptimal inst I x u ∧ violated inst I x = ∅

/-- `Reach inst ν I`: in some run of the algorithm, the `ν`-th solve of Step 1 (iteration `ν`)
takes place with identified pairs `I`. Step 0 sets `ν = t = 0`, so the first solve is `ν = 1`
with no cuts (`I = ∅`). -/
inductive Reach (inst : Instance n1 m1 m2 J) : ℕ → Finset (Fin m2 × Fin J) → Prop
  | start : Reach inst 1 ∅
  | step {ν : ℕ} {I I' : Finset (Fin m2 × Fin J)} :
      Reach inst ν I → Step inst I I' → Reach inst (ν + 1) I'

end MulticutLShaped.SimpleRecourse
