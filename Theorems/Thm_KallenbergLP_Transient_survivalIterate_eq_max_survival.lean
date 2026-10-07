import Definitions.Def_KallenbergLP_Transient_Criteria
set_option autoImplicit false

namespace KallenbergLP.Transient

/-- Lemma 3.2.2, including attainment by the specified reverse sequence of pure rules. -/
theorem survivalIterate_eq_max_survival
    {N : ℕ} {α : Type} [Fintype α] [DecidableEq α]
    (M : MDP N α) (f : ℕ → PureRule M) (R₀ : Policy M)
    (hf : ∀ t : ℕ, 0 < t → ∀ i : Fin N,
      survivalIterate M t i =
        ∑ j : Fin N, M.transition i ((f t).choose i) j * survivalIterate M (t - 1) j) :
    ∀ (t : ℕ) (i : Fin N),
      survivalIterate M t i = survivalProb M (extremalPolicy M f R₀ t) i t ∧
        ∀ R : Policy M, survivalProb M R i t ≤ survivalIterate M t i := by sorry

end KallenbergLP.Transient

