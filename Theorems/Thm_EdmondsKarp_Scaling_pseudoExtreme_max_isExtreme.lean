import Mathlib
import Definitions.Def_EdmondsKarp_Scaling_Transport

namespace EdmondsKarp.Scaling

/-- §2.2, p. 259 (unnumbered): for the Hitchcock problem (`∑ a_i = ∑ b_j`), a pseudo-extreme maximum
flow is extreme. -/
theorem pseudoExtreme_max_isExtreme {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n) (T : Transport m n)
    (ha : ∀ i, 0 < T.a i) (hb : ∀ j, 0 < T.b j) (hsum : ∑ i, T.a i = ∑ j, T.b j)
    (hd : ∀ i j, 0 ≤ T.d i j) (x : Flow m n) (hmax : IsMaxFlow T x)
    (hpe : IsPseudoExtreme T x) :
    IsExtreme T x := by sorry

end EdmondsKarp.Scaling
