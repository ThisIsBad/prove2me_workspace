import Mathlib

open scoped InnerProductSpace

namespace ConvexOptAlg.SVRG

/-- The component assumptions of §6.3: each `fᵢ` is differentiable and convex
on all of `ℝⁿ`, and its declared gradient is `β`-Lipschitz. -/
def SmoothConvexFamily {n m : ℕ}
    (fs : Fin m → EuclideanSpace ℝ (Fin n) → ℝ)
    (gs : Fin m → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (β : ℝ) : Prop :=
  (∀ i x, HasGradientAt (fs i) (gs i x) x) ∧
  (∀ i, ConvexOn ℝ Set.univ (fs i)) ∧
  (∀ i x y, ‖gs i x - gs i y‖ ≤ β * ‖x - y‖)

/-- The uniform average over a finite sample space. In this mission all sample spaces
are nonempty: `Fin m` has `m ≥ 1`, and the spaces of index arrays are then nonempty. -/
noncomputable def uniformMean {A : Type*} [Fintype A] (h : A → ℝ) : ℝ :=
  (∑ a, h a) / (Fintype.card A : ℝ)

/-- The objective `f = (1/m) ∑ᵢ fᵢ` of §6.3. -/
noncomputable def objective {n m : ℕ}
    (fs : Fin m → EuclideanSpace ℝ (Fin n) → ℝ)
    (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  uniformMean (fun i => fs i x)

/-- The average gradient `∇f = (1/m) ∑ᵢ ∇fᵢ`. -/
noncomputable def fullGradient {n m : ℕ}
    (gs : Fin m → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (x : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin n) :=
  ((m : ℝ)⁻¹) • ∑ i, gs i x

/-- The SVRG direction `∇f_i(x) − ∇f_i(y) + ∇f(y)` at anchor `y`. -/
noncomputable def direction {n m : ℕ}
    (gs : Fin m → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (x y : EuclideanSpace ℝ (Fin n)) (i : Fin m) : EuclideanSpace ℝ (Fin n) :=
  gs i x - gs i y + fullGradient gs y

/-- Zero-based implementation of the inner SVRG iterates. `innerIter 0 = x₁ = y` in
the book's numbering, and sample `idx t` produces `innerIter (t+1) = x_{t+2}`.
The value beyond the first `k` updates is held constant; it is never used. -/
noncomputable def innerIter {n m k : ℕ}
    (gs : Fin m → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (η : ℝ) (y : EuclideanSpace ℝ (Fin n)) (idx : Fin k → Fin m) :
    ℕ → EuclideanSpace ℝ (Fin n)
  | 0 => y
  | t + 1 =>
      if ht : t < k then
        innerIter gs η y idx t - η • direction gs (innerIter gs η y idx t) y (idx ⟨t, ht⟩)
      else innerIter gs η y idx t

/-- The epoch output `y⁽ˢ⁺¹⁾ = (1/k) ∑_{t=1}^k x⁽ˢ⁾_t`.
In particular it does not average the final updated point `x_{k+1}`. -/
noncomputable def epochOut {n m : ℕ}
    (gs : Fin m → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (η : ℝ) (k : ℕ) (y : EuclideanSpace ℝ (Fin n)) (idx : Fin k → Fin m) :
    EuclideanSpace ℝ (Fin n) :=
  ((k : ℝ)⁻¹) • ∑ t : Fin k, innerIter gs η y idx t.val

/-- After `s` epochs, with an array of `s` independent index blocks.
`epochOutput 0 = y⁽¹⁾` and `epochOutput s = y⁽ˢ⁺¹⁾`. -/
noncomputable def epochOutput {n m k : ℕ}
    (gs : Fin m → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (η : ℝ) (y₁ : EuclideanSpace ℝ (Fin n)) :
    (s : ℕ) → (Fin s → Fin k → Fin m) → EuclideanSpace ℝ (Fin n)
  | 0, _ => y₁
  | s + 1, idx =>
      epochOut gs η k (epochOutput gs η y₁ s (fun j => idx j.castSucc)) (idx (Fin.last s))

end ConvexOptAlg.SVRG
