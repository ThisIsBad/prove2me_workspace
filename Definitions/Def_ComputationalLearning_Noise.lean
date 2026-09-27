import Definitions.Def_ComputationalLearning_Boosting

/-!
# Kearns and Vazirani, Chapter 5: learning in the presence of noise

Kearns and Vazirani, *An Introduction to Computational Learning Theory*, MIT Press 1994,
doi:10.7551/mitpress/3897.001.0001, Chapter 5 (pp. 103–122).

**The classification noise model (§5.1, p. 104).** The noisy oracle `EX^η_CN(c, D)` draws `x ~ D`
and returns `(x, c(x))` with probability `1 − η` and `(x, ¬c(x))` with probability `η`, the noise
rate `η < 1/2` being fixed and the flips independent.

**Learning from statistics (§5.2, pp. 106–108).** For a literal `z`, `p₀(z)` is the probability that
`z` is set to `0` in a random instance and `p₀₁(z)` the probability that `z` is `0` and the instance
is positive; `z` is *significant* if `p₀(z) ≥ ε/8n` and *harmful* if `p₀₁(z) ≥ ε/8n`; the
conjunction of all significant, non-harmful literals has error at most `ε/2`.

**Statistical queries (§5.3, p. 109).** A statistical query is a predicate `χ : X × {0,1} → {0,1}`
(with a tolerance `τ`); its value is `P_χ = Pr_{x ~ D}[χ(x, c(x)) = 1]`, and the oracle `STAT(c, D)`
returns any estimate within `τ` of it.

**Simulating a query from noisy examples (§5.4.1, pp. 112–113).** Split `X` into `X₁`, the inputs
for which the label matters to `χ` (`χ(x, 0) ≠ χ(x, 1)`), and `X₂`. With `p₁ = D(X₁)`, `D₁` the
conditional of `D` on `X₁`, and probabilities under the noisy oracle, Equation (5.2) reads
`P_χ = p₁ (Pr_{EX_CN(c, D₁)}[χ = 1] − η)/(1 − 2η) + Pr_{EX_CN(c, D)}[χ = 1 ∧ x ∈ X₂]`, every term on
the right being estimable from noisy examples. For hypothesis selection (p. 117), the
probability that `h` disagrees with the noisy label is `γ_h = η + (1 − 2η) error(h)`.
-/

open MeasureTheory ProbabilityTheory

namespace ComputationalLearning

section Noise

variable {X : Type*} [MeasurableSpace X]

/-- The law of one example returned by the **noisy oracle** `EX^η_CN(c, D)`: `x ~ D` and the label
`c(x)` flipped with probability `η`, independently (§5.1, p. 104). -/
noncomputable def noisyExampleLaw (D : Measure X) (c : X → Bool) (η : ℝ) : Measure (X × Bool) :=
  (D.prod (bernoulliMeasure η)).map (fun p : X × Bool ↦ (p.1, if p.2 then !c p.1 else c p.1))

/-- `P_χ = Pr_{x ~ D}[χ(x, c(x)) = 1]`, the value of the statistical query `χ` (§5.3, p. 109). -/
noncomputable def queryProb (D : Measure X) (c : X → Bool) (χ : X × Bool → Bool) : ℝ :=
  (exampleLaw D c {p | χ p = true}).toReal

/-- `X₁`, the inputs on which the label matters to `χ`: `χ(x, 0) ≠ χ(x, 1)` (§5.4.1, p. 112). Its
complement is `X₂`. -/
def labelSensitive (χ : X × Bool → Bool) : Set X :=
  {x | χ (x, false) ≠ χ (x, true)}

end Noise

/-! ### Conjunctions from statistics (§5.2) -/

section Statistics

variable {n : ℕ}

/-- `p₀(z)`: the probability that the literal `z` is set to `0` (does not hold) in a random
instance (p. 107). -/
noncomputable def zeroProb (D : Measure (Cube (Fin n))) (l : Fin n × Bool) : ℝ :=
  (D {a | a l.1 ≠ l.2}).toReal

/-- `p₀₁(z)`: the probability that `z` is set to `0` and the instance is a positive example of the
target (p. 107). -/
noncomputable def zeroPosProb (D : Measure (Cube (Fin n))) (c : Cube (Fin n) → Bool)
    (l : Fin n × Bool) : ℝ :=
  (D {a | a l.1 ≠ l.2 ∧ c a = true}).toReal

/-- The conjunction of all **significant** (`p₀(z) ≥ ε/8n`) literals that are **not harmful**
(`p₀₁(z) < ε/8n`) (p. 107). -/
noncomputable def statisticsConj (D : Measure (Cube (Fin n))) (c : Cube (Fin n) → Bool) (ε : ℝ) :
    Conjunction (Fin n) :=
  Finset.univ.filter (fun l : Fin n × Bool ↦
    ε / (8 * n) ≤ zeroProb D l ∧ zeroPosProb D c l < ε / (8 * n))

end Statistics

end ComputationalLearning
