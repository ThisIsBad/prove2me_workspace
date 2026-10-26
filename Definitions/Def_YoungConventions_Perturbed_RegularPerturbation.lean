import Mathlib
import Definitions.Def_YoungConventions_Perturbed_FiniteChain

open Filter Topology

namespace YoungConventions.Perturbed

/-!
Regular perturbations of a finite Markov chain, conditions (6)–(8), the graph `G` and the
resistance of a transition.
Young (1993), *The Evolution of Conventions*, Econometrica 61:57–84, Appendix, p. 77, PDF p. 22.
-/

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- The transition `x → y` of the family `P^ε` has order `ε^r` (Young 1993, Appendix, condition (8),
p. 77, PDF p. 22): `r ≥ 0` and `ε^{-r} P^ε_{xy}` converges, as `ε → 0⁺`, to a finite limit `c > 0`.

**Formalization Note.** `ε ^ (-r)` is the real power `Real.rpow` (`r` is real, not natural); the
limit is one-sided, `ε → 0` through positive values (`𝓝[>] 0`), because `P^ε` is defined only
for `ε ∈ (0, a]`. "`0 < lim … < ∞`" is the existence of a real limit `c` with `0 < c`. -/
def HasResistance (P : ℝ → Matrix X X ℝ) (x y : X) (r : ℝ) : Prop :=
  0 ≤ r ∧ ∃ c : ℝ, 0 < c ∧ Tendsto (fun ε : ℝ => ε ^ (-r) * P ε x y) (𝓝[>] 0) (𝓝 c)

/-- `P^ε` (`ε ∈ (0, a]`) is a **regular perturbation** of the chain `P⁰` (Young 1993, Appendix,
p. 77, PDF p. 22): `a > 0`, each `P^ε` with `ε ∈ (0, a]` is a Markov chain on `X` (row
stochastic), and for all `x, y ∈ X`
* (6) `P^ε` is aperiodic and irreducible for all `ε ∈ (0, a]`;
* (7) `lim_{ε→0} P^ε_{xy} = P⁰_{xy}`;
* (8) `P^ε_{xy} > 0` for some `ε ∈ (0, a]` implies `∃ r ≥ 0` with `0 < lim_{ε→0} ε^{-r} P^ε_{xy} < ∞`.

**Formalization Note.** The family is a function `P : ℝ → Matrix X X ℝ` that is constrained
only on `ε ∈ (0, a]`; its values elsewhere are irrelevant. Irreducibility is Mathlib's
`Matrix.IsIrreducible`; aperiodicity is `IsAperiodic` (every state has period 1). Limits are
one-sided (`𝓝[>] 0`). In (8) "for some ε" ranges over the parameter interval `(0, a]`. -/
structure IsRegularPerturbation (P0 : Matrix X X ℝ) (P : ℝ → Matrix X X ℝ) (a : ℝ) : Prop where
  pos : 0 < a
  stochastic : ∀ ε ∈ Set.Ioc 0 a, P ε ∈ Matrix.rowStochastic ℝ X
  irreducible : ∀ ε ∈ Set.Ioc 0 a, (P ε).IsIrreducible
  aperiodic : ∀ ε ∈ Set.Ioc 0 a, IsAperiodic (P ε)
  tendsto : ∀ x y : X, Tendsto (fun ε : ℝ => P ε x y) (𝓝[>] 0) (𝓝 (P0 x y))
  order : ∀ x y : X, (∃ ε ∈ Set.Ioc 0 a, 0 < P ε x y) → ∃ r : ℝ, HasResistance P x y r

/-- `(x, y)` is a directed edge of the graph `G` (Young 1993, Appendix, p. 77, PDF p. 22): the
one-period transition `x → y` has positive probability under `P^ε` for all sufficiently small
`ε > 0`. -/
def IsEdge (P : ℝ → Matrix X X ℝ) (x y : X) : Prop :=
  ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < P ε x y

open Classical in
/-- The resistance `r(x, y)` of the transition `x → y` (Young 1993, Appendix, p. 77, PDF p. 22):
the real number `r ≥ 0` of condition (8), i.e. the `r` with `0 < lim_{ε→0} ε^{-r} P^ε_{xy} < ∞`.

**Formalization Note.** Chosen with `Classical.choose`; the paper's uniqueness of `r` is the
milestone `resistance_spec`, so the value does not depend on the choice. When no such `r` exists
the value is the placeholder `0`; it is never used there, because `G`-paths and `G`-trees only
use edges of `G`, which carry a resistance under (8). -/
noncomputable def resistance (P : ℝ → Matrix X X ℝ) (x y : X) : ℝ :=
  if h : ∃ r : ℝ, HasResistance P x y r then Classical.choose h else 0

end YoungConventions.Perturbed
