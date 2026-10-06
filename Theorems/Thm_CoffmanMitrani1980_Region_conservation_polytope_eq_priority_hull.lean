import Definitions.Def_CoffmanMitrani1980_Region_Model

open Finset

namespace CoffmanMitrani1980.Region

/-- **Theorem 2, analytical form** — Coffman and Mitrani, Operations Research 28 (1980), p. 816
(PDF 8), Theorem 2, with p. 817 (PDF 9) "Lemmas 1 and 2 imply that H\* ⊆ H\*\* ⊆ H" and p. 818
(PDF 10) "The equation H\* = H\*\* provides us with an analytical characterization of H\*": a vector
`W` satisfies the conservation law (1) and the `2^M - 2` inequalities (4) if and only if it is a
convex combination `Σ αᵢ Pᵢ` of `M` preemptive priority vectors, as in (3); that is, `H** = H`.

**Formalization Note.** The paper's Theorem 2 is `H* = H`, where H\* is the set of performance
vectors achievable by a scheduling strategy of the class of Assumptions 1–3 (p. 812). That class is
described only in prose, so H\* is replaced by its analytical characterization H\*\*, and the
statement is the part `H** = H` of the chain `H ⊆ H* ⊆ H** ⊆ H` that does not involve strategies.
`0 < M` is needed: for `M = 0`, H is empty (no weights sum to 1) while H\*\* is a point. -/
theorem conservation_polytope_eq_priority_hull {M : ℕ} (hM : 0 < M) (p : Params M) :
    p.Hss = p.H := by sorry

end CoffmanMitrani1980.Region

