import Mathlib

namespace VeinottBaseStock

/-- §3, p. 212: every nonempty closed subset of `ℝⁿ` that is linearly ordered by the
componentwise order and bounded below has a least ("minimal") element. -/
theorem closed_chain_has_least {n : ℕ} (A : Set (Fin n → ℝ)) (hA : IsClosed A)
    (hchain : IsChain (· ≤ ·) A) (hne : A.Nonempty) (hbdd : BddBelow A) :
    ∃ a, IsLeast A a := by sorry

end VeinottBaseStock
