import Mathlib
import Definitions.Def_EdmondsKarp_Scaling_Transport
import Definitions.Def_EdmondsKarp_Scaling_Augmentation
import Definitions.Def_EdmondsKarp_Scaling_Run

namespace EdmondsKarp.Scaling

/-- Proof of Theorem 9 (p. 260): Problem `p` has a maximum flow, and the value `f_p^*` of every
maximum flow of Problem `p` is `min(∑_i [a_i/2^p], ∑_j [b_j/2^p])`. -/
theorem maxFlow_value_problem {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n) (a : Fin m → ℕ)
    (b : Fin n → ℕ) (d : Fin m → Fin n → ℝ) (ha : ∀ i, 0 < a i) (hb : ∀ j, 0 < b j)
    (hsum : ∑ i, a i = ∑ j, b j) (hd : ∀ i j, 0 ≤ d i j) (p : ℕ) :
    (∃ x : Flow m n, IsMaxFlow (problem a b d p) x) ∧
      ∀ x : Flow m n, IsMaxFlow (problem a b d p) x →
        x.ret = ((min (∑ i, a i / 2 ^ p) (∑ j, b j / 2 ^ p) : ℕ) : ℝ) := by sorry

end EdmondsKarp.Scaling
