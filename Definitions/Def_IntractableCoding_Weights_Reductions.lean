import Mathlib
import Definitions.Def_IntractableCoding_Weights_Problems
import Definitions.Def_PricingWithTips_ThreeDM

namespace IntractableCoding.Weights

open PricingWithTips

/-- The triples of a 3DM instance `I = ⟨n, edge⟩` (with `T = Fin n`): the set
`U = {(a, b, c) | edge a b c = true}`, listed in lexicographic order. -/
def triples (I : ThreeDMInstance) : List (Fin I.1 × Fin I.1 × Fin I.1) :=
  ((List.finRange I.1).flatMap fun a => (List.finRange I.1).flatMap fun b =>
    (List.finRange I.1).map fun c => (a, b, c)).filter fun abc => I.2 abc.1 abc.2.1 abc.2.2

/-- `t = |U|`, the number of triples. -/
def tCount (I : ThreeDMInstance) : ℕ := (triples I).length

/-- The `|U| × 3|T|` triple incidence matrix `B` (p. 385): row `r` corresponds to the `r`-th
triple `(a, b, c)` of `triples I` and has weight three, with a `1` in column `a` (first block of
`n` columns), in column `n + b` (second block) and in column `2n + c` (third block). -/
def incidence (I : ThreeDMInstance) : Matrix (Fin (tCount I)) (Fin (3 * I.1)) (ZMod 2) :=
  fun r j =>
    let abc := (triples I).get r
    if j.val = abc.1.val ∨ j.val = I.1 + abc.2.1.val ∨ j.val = 2 * I.1 + abc.2.2.val then 1
    else 0

/-- The COSET WEIGHTS instance of the reduction (p. 385): `A = B`, `y = (11⋯1)`, `w = |T|`. -/
def cosetOf3DM (I : ThreeDMInstance) : CosetInstance :=
  ⟨tCount I, 3 * I.1, incidence I, fun _ => 1, I.1⟩

/-- The top `t` rows of the SUBSPACE WEIGHTS matrix (p. 385): `B` (the first `3n` columns)
followed by `3n` copies of the `t × t` identity matrix; column `3n + k t + i` (`0 ≤ k < 3n`,
`0 ≤ i < t`) is the `i`-th column of the `k`-th copy. -/
def subspaceTop (I : ThreeDMInstance) :
    Matrix (Fin (tCount I)) (Fin (3 * I.1 * (tCount I + 1))) (ZMod 2) :=
  fun r j =>
    if hj : j.val < 3 * I.1 then incidence I r ⟨j.val, hj⟩
    else if (j.val - 3 * I.1) % tCount I = r.val then 1 else 0

/-- The `(3nt + 3n + t) × (3nt + 3n)` matrix `A` of the SUBSPACE WEIGHTS reduction (p. 385):
the top `t` rows are `subspaceTop I` = `[B | I_t | ⋯ | I_t]`, the lower `3n(t + 1)` rows form
the identity matrix `I_{3n(t+1)}`. -/
def subspaceMatrix (I : ThreeDMInstance) :
    Matrix (Fin (tCount I + 3 * I.1 * (tCount I + 1))) (Fin (3 * I.1 * (tCount I + 1)))
      (ZMod 2) :=
  Matrix.of (Fin.append (subspaceTop I) (1 : Matrix (Fin (3 * I.1 * (tCount I + 1)))
    (Fin (3 * I.1 * (tCount I + 1))) (ZMod 2)))

/-- The number of rows of `subspaceMatrix I` is the paper's `3nt + 3n + t`. -/
theorem subspaceMatrix_rows (I : ThreeDMInstance) :
    tCount I + 3 * I.1 * (tCount I + 1) = 3 * I.1 * tCount I + 3 * I.1 + tCount I := by ring

/-- The number of columns of `subspaceMatrix I` is the paper's `3nt + 3n`. -/
theorem subspaceMatrix_cols (I : ThreeDMInstance) :
    3 * I.1 * (tCount I + 1) = 3 * I.1 * tCount I + 3 * I.1 := by ring

/-- The SUBSPACE WEIGHTS instance of the reduction (pp. 385–386): the matrix `A` above and
`w = 3n² + 4n` with `n = |T|`. -/
def subspaceOf3DM (I : ThreeDMInstance) : SubspaceInstance :=
  ⟨tCount I + 3 * I.1 * (tCount I + 1), 3 * I.1 * (tCount I + 1), subspaceMatrix I,
    3 * I.1 ^ 2 + 4 * I.1⟩

/-- `x₀`: the vector of length `t` formed from the first `t` components of `x`. -/
def firstPart (I : ThreeDMInstance)
    (x : Fin (tCount I + 3 * I.1 * (tCount I + 1)) → ZMod 2) : Fin (tCount I) → ZMod 2 :=
  fun i => x (Fin.castAdd (3 * I.1 * (tCount I + 1)) i)

/-- `x₁`: the vector formed from the last `3n(t + 1)` components of `x`. -/
def lastPart (I : ThreeDMInstance)
    (x : Fin (tCount I + 3 * I.1 * (tCount I + 1)) → ZMod 2) :
    Fin (3 * I.1 * (tCount I + 1)) → ZMod 2 :=
  fun i => x (Fin.natAdd (tCount I) i)

end IntractableCoding.Weights
