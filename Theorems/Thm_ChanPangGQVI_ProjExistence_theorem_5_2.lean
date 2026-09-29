import Mathlib
import Definitions.Def_ChanPangGQVI_Shared_GQVI

namespace ChanPangGQVI.ProjExistence

/-- **Theorem 5.2** (Chan and Pang 1982, p. 220). Let `f` and `K` be respectively a point-to-point
and a point-to-set mapping of `ℝⁿ` into itself. Suppose that there exists a nonempty compact
convex set `C` such that
(i) `K(C) ⊆ C`;
(ii) `f` is continuous on `C`;
(iii) `K` is a nonempty continuous convex valued mapping on `C`.
Then `GQVI(K, f)` has a solution.

"Continuous on `C`" for `K` is upper and lower semicontinuity at every point of `C` with
neighbourhoods relative to `C` (Mathlib `UpperHemicontinuousOn` / `LowerHemicontinuousOn`).

Implicit hypothesis made explicit: `K(x)` is closed for every `x ∈ C`. The paper uses Berge's
definitions, under which upper semicontinuous mappings have compact values, and its proof says
"the continuity of `K` implies that each set `K(x)` is closed". Without it the statement is false:
`C = [0, 1]`, `K(x) ≡ (0, 1)`, `f ≡ 1`. -/
theorem theorem_5_2 {n : ℕ}
    (K : EuclideanSpace ℝ (Fin n) → Set (EuclideanSpace ℝ (Fin n)))
    (f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (C : Set (EuclideanSpace ℝ (Fin n)))
    (hC_nonempty : C.Nonempty) (hC_compact : IsCompact C) (hC_convex : Convex ℝ C)
    (h_i : ∀ x ∈ C, K x ⊆ C)
    (h_ii : ContinuousOn f C)
    (h_iii_nonempty : ∀ x ∈ C, (K x).Nonempty)
    (h_iii_upper : UpperHemicontinuousOn K C) (h_iii_lower : LowerHemicontinuousOn K C)
    (h_iii_convex : ∀ x ∈ C, Convex ℝ (K x))
    (hK_closed : ∀ x ∈ C, IsClosed (K x)) :
    ∃ x y, ChanPangGQVI.Shared.IsGQVISolution K (fun z => {f z}) x y := by sorry

end ChanPangGQVI.ProjExistence

