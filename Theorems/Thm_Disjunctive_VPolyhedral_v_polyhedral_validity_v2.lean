import Mathlib
import Definitions.Def_Disjunctive_VPolyhedral_Basic


namespace Disjunctive.VPolyhedral

/-- Proposition 12.1 (Balas, *Disjunctive Programming*, Springer 2018, §12, p. 195): for the
V-polyhedral disjunctive set `F := ⋃_{h∈Q} P^h`, `P^h = conv V^h + cone R^h`, over a finite index
set `Q` whose disjuncts are all nonempty (every `V^h ≠ ∅`), the inequality `αx ≥ β` is valid for
`F` if and only if `αp ≥ β` for every `p ∈ V^h` and `αr ≥ 0` for every `r ∈ R^h`, `h ∈ Q`.

Correction w.r.t. the retired version: the book's standing assumption that every disjunct
`P^h` is nonempty (has at least one vertex) is now the instance hypothesis
`[∀ h, Nonempty (Vidx h)]`; with `V^h = ∅` the set `P^h` is empty while its rays still
constrain `α`. -/
theorem v_polyhedral_validity_v2 {n : ℕ} {Q : Type*} [Fintype Q] (Vidx Ridx : Q → Type*)
    [∀ h, Fintype (Vidx h)] [∀ h, Fintype (Ridx h)] [∀ h, Nonempty (Vidx h)]
    (vpt : ∀ h, Vidx h → Fin n → ℝ)
    (rvec : ∀ h, Ridx h → Fin n → ℝ) (alpha : Fin n → ℝ) (beta : ℝ) :
    (∀ x ∈ DisjSet Vidx Ridx vpt rvec, beta ≤ dotProduct alpha x) ↔
      IsVPolyhedralValid Vidx Ridx vpt rvec alpha beta := by sorry

end Disjunctive.VPolyhedral

