import Mathlib
import Definitions.Def_SendSplit_DPEquations_Network
import Definitions.Def_SendSplit_DPEquations_Subproblem

namespace SendSplit.DPEquations

/-- `(i, j) ∈ A_I` (p. 640): `A_I = A` if `r_I > 0`, and `A_I = {(i, j) : (j, i) ∈ A}` if
`r_I < 0`. (`A_I` is only used when `r_I ≠ 0`.) -/
def IsSendArc {n : ℕ} (A : Finset (Fin n × Fin n)) (r : Fin n → ℝ) (I : Finset (Fin n))
    (i j : Fin n) : Prop :=
  (0 < demandSum r I ∧ (i, j) ∈ A) ∨ (demandSum r I < 0 ∧ (j, i) ∈ A)

/-- The cost `c_ij(r_I)` of sending `r_I` units from `i` to `j` along an arc of `A_I`
(p. 640): `c_ij(r_I)` if `r_I > 0` and `(i, j) ∈ A`; `c_ji(-r_I)` if `r_I < 0` and
`(j, i) ∈ A`; and `+∞` when `(i, j) ∉ A_I`, so that a minimum over `A_I` is a minimum over
all nodes `j`. -/
noncomputable def sendCost {n : ℕ} (A : Finset (Fin n × Fin n)) (c : Fin n → Fin n → ℝ → ℝ)
    (r : Fin n → ℝ) (I : Finset (Fin n)) (i j : Fin n) : EReal :=
  if 0 < demandSum r I ∧ (i, j) ∈ A then ((c i j (demandSum r I) : ℝ) : EReal)
  else if demandSum r I < 0 ∧ (j, i) ∈ A then ((c j i (-demandSum r I) : ℝ) : EReal)
  else ⊤

/-- `B_iI` computed from an array `C'` by (3) (p. 641): for `|I| > 1`,
`B_iI = min_{∅ ⊂ J ⊂ I} [C'_iJ + C'_{i, I \ J}]` over nonempty proper subsets `J`; for
`|I| = 1`, `B_iI = 0` if `I = {i}` and `+∞` otherwise. -/
noncomputable def splitCost {n : ℕ} (C' : Fin n → Finset (Fin n) → EReal) (i : Fin n)
    (I : Finset (Fin n)) : EReal :=
  if I.card = 1 then (if I = {i} then 0 else ⊤)
  else (I.powerset.filter (fun J => J.Nonempty ∧ J ≠ I)).inf
    (fun J => C' i J + C' i (I \ J))

/-- A `+∞`-or-real-valued solution of (1) and (2), with `B` defined by (3) (pp. 640–641):
an array `C'_jI` (`j ∈ N`, `∅ ⊂ I ⊆ D`; values at other `I` are irrelevant) such that every
entry is `+∞` or real, and for every node `i` and every `∅ ⊂ I ⊆ D`:
(1) if `r_I = 0` then `C'_iI = C'_{j, I \ {j}}` for all `j ∈ I`;
(2) if `r_I ≠ 0` then `C'_iI = min_{(i,j) ∈ A_I} [c_ij(r_I) + C'_jI] ∧ B'_iI`. -/
def IsSolution {n : ℕ} (A : Finset (Fin n × Fin n)) (c : Fin n → Fin n → ℝ → ℝ)
    (r : Fin n → ℝ) (C' : Fin n → Finset (Fin n) → EReal) : Prop :=
  (∀ j I, IsAdmissible r I → C' j I ≠ ⊥) ∧
  ∀ i I, IsAdmissible r I →
    (demandSum r I = 0 → ∀ j ∈ I, C' i I = C' j (I.erase j)) ∧
    (demandSum r I ≠ 0 →
      C' i I = (Finset.univ.inf fun j => sendCost A c r I i j + C' j I) ⊓ splitCost C' i I)

end SendSplit.DPEquations
