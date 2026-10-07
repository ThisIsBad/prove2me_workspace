import Definitions.Def_KallenbergLP_Transient_Criteria
set_option autoImplicit false

namespace KallenbergLP.Transient

/-- Theorem 3.2.4: five characterizations of a transient dynamic program. -/
theorem fiveEquivalentCharacterizations
    {N : ℕ} {α : Type} [Fintype α] [DecidableEq α]
    (M : MDP N α) (β : Fin N → ℝ) (hβ : ∀ j, 0 < β j) :
    ((∀ f : PureRule M, IsTransient M (purePolicy M f)) ↔
       (∀ R : Policy M, IsTransient M R)) ∧
    ((∀ R : Policy M, IsTransient M R) ↔
       (∀ i : Fin N, survivalIterate M N i < 1)) ∧
    ((∀ i : Fin N, survivalIterate M N i < 1) ↔ Contracting M) ∧
    (Contracting M ↔ LPFinite M β) := by sorry

end KallenbergLP.Transient

