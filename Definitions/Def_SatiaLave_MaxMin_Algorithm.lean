import Mathlib
import Definitions.Def_SatiaLave_MaxMin_Model

namespace SatiaLave.MaxMin

open Finset

variable {S : Type*} [Fintype S] [DecidableEq S] {D : S → Type*}

/-- One iteration of Phase 1, the policy-evaluation routine (Satia–Lave 1973, p. 730, (a)–(b)
and (6)), for a fixed policy `A`: starting from nature's current choice `P`, the new choice
`P'` uses, in every state `i`, a row `p_i'^A ∈ S_i^A` that minimizes
`Σ_j p_ij (r^A_ij + β v^A_j)` over `S_i^A`, where `v^A` is the present value of `A` under `P`.
Rows of `P'` at decisions other than `A i` are unconstrained. -/
def IsPhase1Step (M : UncertainMDP S D) (A : Policy S D) (P P' : Sel M) : Prop :=
  ∀ i, ∀ q ∈ M.U i (A i),
    ∑ j, P'.1 i (A i) j * (M.r i (A i) j + M.β * presentValue M A P j) ≤
      ∑ j, q j * (M.r i (A i) j + M.β * presentValue M A P j)

/-- The stopping test of Phase 1 (p. 730): the new rows reproduce the current present values,
`Σ_j p'^A_ij (r^A_ij + β v^A_j) = v^A_i` for every state `i`; then the routine proceeds to
Phase 2. -/
def Phase1Stops (M : UncertainMDP S D) (A : Policy S D) (P P' : Sel M) : Prop :=
  ∀ i, ∑ j, P'.1 i (A i) j * (M.r i (A i) j + M.β * presentValue M A P j) =
    presentValue M A P i

/-- The Phase 2 test quantity, cited as (7) (p. 730): for a value vector `v`, state `i` and
decision `k`, the minimum over `p ∈ S_i^k` of `Σ_j p_j (r^k_ij + β v_j)`. -/
noncomputable def test7 (M : UncertainMDP S D) (v : S → ℝ) (i : S) (k : D i) : ℝ :=
  ⨅ p : M.U i k, ∑ j, (p : S → ℝ) j * (M.r i k j + M.β * v j)

variable [∀ i, Fintype (D i)] [∀ i, Nonempty (D i)]

/-- One iteration of Phase 2, the policy-improvement routine (p. 730), from policy `A` to
policy `B`, with Phase 1 taken to be exact (it returns nature's minimum `robustValue M A`):
in every state `i`, `B i` maximizes `test7 (robustValue M A) i k` over the decisions `k`, and
`B i = A i` whenever `A i` is itself a maximizer (the retention rule of Howard's algorithm). -/
def IsPhase2Step (M : UncertainMDP S D) (A B : Policy S D) : Prop :=
  ∀ i, test7 M (robustValue M A) i (B i) =
      (Finset.univ : Finset (D i)).sup' Finset.univ_nonempty (test7 M (robustValue M A) i) ∧
    (test7 M (robustValue M A) i (A i) =
        (Finset.univ : Finset (D i)).sup' Finset.univ_nonempty (test7 M (robustValue M A) i) →
      B i = A i)

end SatiaLave.MaxMin
