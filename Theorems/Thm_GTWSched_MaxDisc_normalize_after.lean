import Mathlib
import Definitions.Def_GTWSched_MaxDisc_Model

namespace GTWSched.MaxDisc

theorem normalize_after {N : ℕ} (r d l : Fin N → ℝ) (α : ℝ) (hα : 0 ≤ α)
    (hr : ∀ i, 0 ≤ r i) (hl : ∀ i, 0 ≤ l i) (hsf : SpecialForm r d l α)
    (hd : Monotone d) (n : Fin N) (hnlast : n.val + 1 = N)
    (σ : Fin N ≃ Fin N) (s : Fin N → ℝ)
    (hopt : Optimum r d l σ s) (hrtp : ReleaseTimeProperty r σ s n) :
    ∃ (σ' : Fin N ≃ Fin N) (s' : Fin N → ℝ),
      Optimum r d l σ' s' ∧ ReleaseTimeProperty r σ' s' n ∧
      σ'.symm n = σ.symm n ∧
      (∀ p : Fin N, p < σ.symm n → σ' p = σ p ∧ s' (σ p) = s (σ p)) ∧
      s' n ≤ s n ∧
      s' n = max (r n) (⨆ i : {i : Fin N // σ'.symm i < σ'.symm n}, s' i.1 + l i.1) ∧
      (∀ p q : Fin N, σ'.symm n < p → p < q → σ' p < σ' q) ∧
      (∀ p q : Fin N, σ'.symm n ≤ p → q.val = p.val + 1 →
        s' (σ' q) = s' (σ' p) + l (σ' p)) := by sorry

end GTWSched.MaxDisc

