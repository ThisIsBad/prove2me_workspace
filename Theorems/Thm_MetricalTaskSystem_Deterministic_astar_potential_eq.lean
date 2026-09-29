import Mathlib
import Definitions.Def_MetricalTaskSystem_Deterministic_Model
import Definitions.Def_MetricalTaskSystem_Deterministic_AstarD

namespace MetricalTaskSystem.Deterministic

/-- **Lemma 6.4** (Borodin–Linial–Saks 1992, p. 756). Let `F_k = 2 Σ_{x ≠ s_k} f_k(x) + f_k(s_k)`.
Then `F_k = C_{k−1} + Σ_{i=1}^k d(s_i, s_{i−1})`, where `C_{k−1} = Σ_{i=0}^{k−1} c_i`
(for `k = 0` both sides are `0`). -/
theorem astar_potential_eq {S : Type} [Fintype S] [DecidableEq S] [Nontrivial S]
    (d : S → S → ℝ) (hd : IsTaskSystem d) (s₀ : S) (s : ℕ → S) (hs : IsAstarSeq d s₀ s)
    (k : ℕ) :
    2 * ∑ x ∈ Finset.univ.erase (s k), fSeq d s k x + fSeq d s k (s k) =
      ∑ i ∈ Finset.range k, cSeq d s i + ∑ i ∈ Finset.range k, d (s (i + 1)) (s i) := by sorry

end MetricalTaskSystem.Deterministic
