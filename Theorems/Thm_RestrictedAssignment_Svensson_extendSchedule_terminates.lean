import Mathlib
import Definitions.Def_RestrictedAssignment_Svensson_configLP
import Definitions.Def_RestrictedAssignment_Svensson_extendSchedule

namespace RestrictedAssignment.Svensson

/-- Svensson, arXiv:1011.1168v2, p. 19, Lemma 4.9: Algorithm 2 terminates — it has no infinite
run, whatever potential move of minimum value is chosen in each iteration. Stated for positive
job sizes: with a job of size 0 the printed statement fails (see the natural-language
statement). -/
theorem extendSchedule_terminates {J M : Type} [Fintype J] [Fintype M] [DecidableEq J] [DecidableEq M]
    (Γ : J → Finset M) (p : J → ℝ) (hp : ∀ j, 0 < p j)
    (σ0 : J → Option M) (jnew : J) (hσ0 : Valid Γ p σ0) (hjnew : σ0 jnew = none) :
    ¬ ∃ f : ℕ → AlgState J M,
        f 0 = initState σ0 jnew ∧ ∀ n, Step Γ p jnew (f n) (f (n + 1)) := by sorry

end RestrictedAssignment.Svensson
