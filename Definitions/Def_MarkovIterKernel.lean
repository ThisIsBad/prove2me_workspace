import Mathlib.Probability.Kernel.Basic
import Mathlib.Probability.Kernel.Composition.Comp

/-!
The `n`-step transition kernel of a Markov kernel.

Source: Galin L. Jones, *On the Markov Chain Central Limit Theorem*,
Probability Surveys 1 (2004) 299-320 (arXiv math/0409112v2), §2: the `n`-step
kernel `Pⁿ(x, dy)`.
-/

open ProbabilityTheory

namespace MarkovChainCLT

/-- The `n`-step transition kernel `Pⁿ` of a Markov transition kernel `P`:
`iterKernel P 0` is the identity (Dirac) kernel and
`iterKernel P (n+1) = P ∘ₖ iterKernel P n`. -/
noncomputable def iterKernel {X : Type*} [MeasurableSpace X] (P : Kernel X X) :
    ℕ → Kernel X X
  | 0 => Kernel.id
  | n + 1 => P ∘ₖ iterKernel P n

@[simp] lemma iterKernel_zero {X : Type*} [MeasurableSpace X] (P : Kernel X X) :
    iterKernel P 0 = Kernel.id := rfl

@[simp] lemma iterKernel_succ {X : Type*} [MeasurableSpace X] (P : Kernel X X) (n : ℕ) :
    iterKernel P (n + 1) = P ∘ₖ iterKernel P n := rfl

instance iterKernel.instIsMarkovKernel {X : Type*} [MeasurableSpace X]
    (P : Kernel X X) [IsMarkovKernel P] (n : ℕ) : IsMarkovKernel (iterKernel P n) := by
  induction n with
  | zero => rw [iterKernel_zero]; infer_instance
  | succ n ih => rw [iterKernel_succ]; exact Kernel.IsMarkovKernel.comp _ _

end MarkovChainCLT
