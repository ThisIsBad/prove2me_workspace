import Mathlib
import Definitions.Def_NonmonotoneSubmod_Shared_OPT
import Definitions.Def_NonmonotoneSubmod_SmoothLS_BiasedSample

namespace NonmonotoneSubmod.SmoothLS

variable {X : Type} [Fintype X] [DecidableEq X]

/-- The estimate `est` of `ω_{A,δ}` used in step 2 of Algorithm SLS (p. 1142) is accurate
"within `± (1/n²) OPT`", where `n = |X|`: `|est x - ω_{A,δ}(x)| ≤ OPT / n²` for every `x`. -/
def Accurate (f : Finset X → ℝ) (δ : ℝ) (A : Finset X) (est : X → ℝ) : Prop :=
  ∀ x : X, |est x - omegaB f A δ x| ≤ NonmonotoneSubmod.Shared.OPT f / (Fintype.card X : ℝ) ^ 2

/-- One iteration of Algorithm SLS (steps 3 and 4, p. 1142), given the current set `A`, the
current estimates `est` of `ω_{A,δ}`, and the next set `A'`, with `n = |X|`:
* step 3: some `x ∉ A` has `est x > (2/n²) OPT`, and `A' = A ∪ {x}`;
* step 4 (reached only when step 3 does not apply, i.e. `est x ≤ (2/n²) OPT` for every
  `x ∉ A`): some `x ∈ A` has `est x < -(2/n²) OPT`, and `A' = A \ {x}`.
Any such `x` may be chosen. -/
def SLSStep (f : Finset X → ℝ) (est : X → ℝ) (A A' : Finset X) : Prop :=
  (∃ x, x ∉ A ∧ 2 / (Fintype.card X : ℝ) ^ 2 * NonmonotoneSubmod.Shared.OPT f < est x ∧ A' = insert x A) ∨
  ((∀ x, x ∉ A → est x ≤ 2 / (Fintype.card X : ℝ) ^ 2 * NonmonotoneSubmod.Shared.OPT f) ∧
    ∃ x, x ∈ A ∧ est x < -(2 / (Fintype.card X : ℝ) ^ 2 * NonmonotoneSubmod.Shared.OPT f) ∧ A' = A.erase x)

/-- Algorithm SLS has terminated at `A` with estimates `est` (it reaches step 5): neither step 3
nor step 4 applies. -/
def SLSTerminated (f : Finset X → ℝ) (est : X → ℝ) (A : Finset X) : Prop :=
  ¬ ∃ A' : Finset X, SLSStep f est A A'

end NonmonotoneSubmod.SmoothLS
