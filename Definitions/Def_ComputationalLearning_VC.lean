import Mathlib.Data.Nat.Lattice
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Definitions.Def_ComputationalLearning_Occam

/-!
# Kearns and Vazirani, Chapter 3: the Vapnik–Chervonenkis dimension

Kearns and Vazirani, *An Introduction to Computational Learning Theory*, MIT Press 1994,
doi:10.7551/mitpress/3897.001.0001, Chapter 3 (pp. 49–72).

For a concept class `C` over `X` and a finite `S ⊆ X`, `Π_C(S) = {c ∩ S : c ∈ C}` is the set of
dichotomies of `S` realized by `C` (Definition 7, p. 50); `S` is **shattered** if `Π_C(S)` is all
of `2^S` (Definition 8); the **VC dimension** `VCD(C)` is the cardinality of the largest shattered
set, `∞` if arbitrarily large finite sets are shattered (Definition 9, p. 51). `Π_C(m)` is the
maximum of `|Π_C(S)|` over `|S| = m` (Definition 10, p. 54), and `Φ_d(m)` is defined by
`Φ_d(m) = Φ_d(m−1) + Φ_{d−1}(m−1)`, `Φ_d(0) = Φ_0(m) = 1` (Definition 11, p. 55). For a target
`c`, the **error regions** are `Δ(c) = {c Δ c' : c' ∈ C}`, and a set `S` is an **ε-net** for
`Δ_ε(c)` if it hits every error region of weight at least `ε` under `D` (Definition 12, p. 58).
-/

open MeasureTheory

namespace ComputationalLearning

section VC

variable {X : Type*} [MeasurableSpace X]

/-- `Π_C(S)`, the dichotomies of the finite set `S` realized by `C`: the functions `S → {0,1}` that
are restrictions of concepts of `C` (Definition 7). -/
def restrictions (C : Set (X → Bool)) (S : Finset X) : Set (S → Bool) :=
  {f | ∃ c ∈ C, ∀ x : S, f x = c x}

/-- `S` is **shattered** by `C`: every dichotomy of `S` is realized (Definition 8). -/
def Shatters (C : Set (X → Bool)) (S : Finset X) : Prop :=
  ∀ f : S → Bool, ∃ c ∈ C, ∀ x : S, c x = f x

/-- The **Vapnik–Chervonenkis dimension** of `C` (Definition 9): the supremum of the cardinalities
of the finite sets shattered by `C`, in `ℕ∞` (`∞` if arbitrarily large finite sets are shattered;
`0` if only the empty set is). -/
noncomputable def vcDim (C : Set (X → Bool)) : ℕ∞ :=
  ⨆ (S : Finset X) (_ : Shatters C S), (S.card : ℕ∞)

/-- `Π_C(m) = max{|Π_C(S)| : |S| = m}` (Definition 10), as a supremum in `ℕ` (it is at most
`2^m`). -/
noncomputable def growth (C : Set (X → Bool)) (m : ℕ) : ℕ :=
  ⨆ (S : Finset X) (_ : S.card = m), (restrictions C S).ncard

/-- `Φ_d(m)` (Definition 11): `Φ_d(m) = Φ_d(m − 1) + Φ_{d−1}(m − 1)` with `Φ_d(0) = Φ_0(m) = 1`. -/
def Phi : ℕ → ℕ → ℕ
  | 0, _ => 1
  | _ + 1, 0 => 1
  | d + 1, m + 1 => Phi (d + 1) m + Phi d m

/-- The error region `c Δ c' = {x : c(x) ≠ c'(x)}` of the hypothesis `c'` with respect to the target
`c` (p. 57). -/
def errorRegion (c c' : X → Bool) : Set X :=
  {x | c' x ≠ c x}

/-- The points of a labeled sample. -/
noncomputable def samplePoints {m : ℕ} (S : Fin m → X × Bool) : Finset X := by
  classical exact Finset.univ.image (fun i ↦ (S i).1)

/-- `S` is an **ε-net** for `Δ_ε(c)` (Definition 12, p. 58): every error region `c Δ h`, `h ∈ H`, of
weight at least `ε` under `D` contains a point of `S`. -/
def IsEpsNet (H : Set (X → Bool)) (c : X → Bool) (D : Measure X) (ε : ℝ) (S : Finset X) :
    Prop :=
  ∀ h ∈ H, ENNReal.ofReal ε ≤ D (errorRegion c h) → ∃ x ∈ S, x ∈ errorRegion c h

/-- The double-sample event of the proof of Theorem 3.3 (§3.5.2, pp. 59–61), on the points of two
samples `S₁, S₂` of size `m`: some `h ∈ H` agrees with the target `c` on every point of `S₁` (it is
consistent with the first sample) and disagrees with `c` on at least `εm/2` points of `S₂`. -/
def doubleSampleEvent (H : Set (X → Bool)) (c : X → Bool) (ε : ℝ) (m : ℕ) :
    Set ((Fin m → X) × (Fin m → X)) :=
  {p | ∃ h ∈ H, (∀ i, h (p.1 i) = c (p.1 i)) ∧
    ε * m / 2 ≤ ((Finset.univ.filter fun i ↦ h (p.2 i) ≠ c (p.2 i)).card : ℝ)}

/-- `H` is **well-behaved** for the target `c` (Blumer, Ehrenfeucht, Haussler and Warmuth, J. ACM
1989): for every distribution `D` and all `ε`, `m`, the double-sample event is null-measurable for
the law `Dᵐ ⊗ Dᵐ` of two independent samples. The proof of Theorem 3.3 uses this (it integrates
over the double sample); the book leaves it implicit. It holds for every countable class of
measurable concepts. Without it Theorem 3.3 is false: on `X = ω₁` with the countable–cocountable
σ-algebra and the measure that is `1` on co-countable sets, the final segments `(α, ω₁)` together
with the empty concept have VC dimension `1`, yet no finite sample is an ε-net for the target `∅`,
since `(max S, ω₁)` has weight `1`. -/
def IsWellBehaved (H : Set (X → Bool)) (c : X → Bool) : Prop :=
  ∀ D : Measure X, IsProbabilityMeasure D → ∀ (ε : ℝ) (m : ℕ),
    NullMeasurableSet (doubleSampleEvent H c ε m)
      ((Measure.pi fun _ : Fin m ↦ D).prod (Measure.pi fun _ : Fin m ↦ D))

end VC

end ComputationalLearning
