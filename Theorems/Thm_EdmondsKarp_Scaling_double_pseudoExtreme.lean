import Mathlib
import Definitions.Def_EdmondsKarp_Scaling_Transport
import Definitions.Def_EdmondsKarp_Scaling_Augmentation
import Definitions.Def_EdmondsKarp_Scaling_Run

namespace EdmondsKarp.Scaling

/-- Lemma 3 (p. 260): if `f` is a pseudo-extreme flow in Problem `p` (`p ≥ 1`), then `2f` is a
pseudo-extreme flow in Problem `p - 1`. -/
theorem double_pseudoExtreme {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n) (a : Fin m → ℕ) (b : Fin n → ℕ)
    (d : Fin m → Fin n → ℝ) (ha : ∀ i, 0 < a i) (hb : ∀ j, 0 < b j)
    (hsum : ∑ i, a i = ∑ j, b j) (hd : ∀ i j, 0 ≤ d i j) (p : ℕ) (hp : 1 ≤ p) (x : Flow m n)
    (hx : IsPseudoExtreme (problem a b d p) x) :
    IsPseudoExtreme (problem a b d (p - 1)) ((2 : ℝ) • x) := by sorry

end EdmondsKarp.Scaling
