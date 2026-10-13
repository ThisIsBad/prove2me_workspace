import Mathlib
import Definitions.Def_BertsekasShreve_BorelFinite_Policy
import Definitions.Def_BertsekasShreve_FiniteHorizon_SpecificModels

namespace BertsekasShreve.ImperfectInfo

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal Classical

/-- Definition 7.7 (p. 118): a topological space `X` is a *Borel space* if it is homeomorphic
to a Borel subset of a complete separable metric (Polish) space. The empty space qualifies. -/
def IsBorelSpace (X : Type) [TopologicalSpace X] : Prop :=
  ∃ (Y : Type) (_ : TopologicalSpace Y), PolishSpace Y ∧
    ∃ e : X → Y, Topology.IsEmbedding e ∧ MeasurableSet[borel Y] (Set.range e)

/-- Definitions 7.18 and 7.20 (p. 171): `f` is *universally measurable* if the preimage of every
measurable set lies in the completion of every probability measure on the domain. -/
def UnivMeasurable {α β : Type} [MeasurableSpace α] [MeasurableSpace β] (f : α → β) : Prop :=
  ∀ ν : Measure α, IsProbabilityMeasure ν → NullMeasurable f ν

/-- Definition 7.21 (p. 177): `f : D → R*` is *lower semianalytic* if `D` is analytic and every
strict lower level set `{x ∈ D | f x < c}`, `c ∈ ℝ`, is analytic. Values of `f` outside `D` are
irrelevant. -/
def LowerSemianalyticOn {α : Type} [TopologicalSpace α] (f : α → EReal) (D : Set α) : Prop :=
  MeasureTheory.AnalyticSet D ∧ ∀ c : ℝ, MeasureTheory.AnalyticSet {x | x ∈ D ∧ f x < (c : EReal)}

/-- Positive part `x⁺ = max(x, 0)` of an extended real, as an element of `[0, ∞]`. -/
noncomputable def posPart (x : EReal) : ℝ≥0∞ := x.toENNReal

/-- Negative part `x⁻ = max(-x, 0)` of an extended real, as an element of `[0, ∞]`. -/
noncomputable def negPart (x : EReal) : ℝ≥0∞ := (-x).toENNReal

/-- The book's extended integral, eq. (43) of Chapter 7 (p. 139):
`∫ f dp = ∫ f⁺ dp − ∫ f⁻ dp` with the convention `∞ − ∞ = +∞` (eq. (42)). -/
noncomputable def extIntegral {α : Type} [MeasurableSpace α] (μ : Measure α) (f : α → EReal) :
    EReal :=
  if ∫⁻ a, posPart (f a) ∂μ = ∞ then ⊤
  else ((∫⁻ a, posPart (f a) ∂μ : ℝ≥0∞) : EReal) - ((∫⁻ a, negPart (f a) ∂μ : ℝ≥0∞) : EReal)

/-- `f` is *quasi-integrable* for `μ`: `∫ f⁺ dμ < ∞` or `∫ f⁻ dμ < ∞` (p. 246). -/
def QuasiIntegrable {α : Type} [MeasurableSpace α] (μ : Measure α) (f : α → EReal) : Prop :=
  ∫⁻ a, posPart (f a) ∂μ < ∞ ∨ ∫⁻ a, negPart (f a) ∂μ < ∞

/-! ### Histories of a controlled process with stage-dependent state spaces

A process has state space `X j` at stage `j` and a fixed control space `C`. -/

/-- States `y₀, …, yₙ` of stages `0, …, n`. -/
abbrev StateSeq (X : ℕ → Type) (n : ℕ) := (m : Fin (n + 1)) → X m

/-- What the controller has seen at stage `n`: `(y₀, u₀, …, u_{n−1}, yₙ)`. -/
abbrev Obs (X : ℕ → Type) (C : Type) (n : ℕ) := StateSeq X n × (Fin n → C)

/-- A history `(y₀, u₀, …, yₙ, uₙ)` up to and including the control of stage `n`. -/
abbrev Hist (X : ℕ → Type) (C : Type) (n : ℕ) := StateSeq X n × (Fin (n + 1) → C)

variable {X : ℕ → Type} {C : Type}

/-- The state `yₙ` of the last stage of a history. -/
def Hist.state {n : ℕ} (h : Hist X C n) : X n := h.1 (Fin.last n)

/-- The control `uₙ` of the last stage of a history. -/
def Hist.control {n : ℕ} (h : Hist X C n) : C := h.2 (Fin.last n)

/-- The observation `(y₀, u₀, …, yₙ)` contained in a history (drop the last control). -/
def Hist.obs {n : ℕ} (h : Hist X C n) : Obs X C n := (h.1, fun j => h.2 j.castSucc)

/-- The history of stages `0, …, n` contained in a history of stages `0, …, n+1`. -/
def Hist.prefix {n : ℕ} (h : Hist X C (n + 1)) : Hist X C n :=
  (fun m => h.1 m.castSucc, fun j => h.2 j.castSucc)

/-- Extend a history of stages `0, …, n` by the next state `y_{n+1}`. -/
def Hist.extend {n : ℕ} (h : Hist X C n) (y : X (n + 1)) : Obs X C (n + 1) :=
  (Fin.snoc (α := fun m : Fin (n + 2) => X m) h.1 y, h.2)

/-- The stage-0 observation `(y₀)`. -/
def Obs.init (y : X 0) : Obs X C 0 :=
  (Fin.snoc (α := fun m : Fin 1 => X m) (fun i => Fin.elim0 i) y, fun i => Fin.elim0 i)

variable [∀ j, MeasurableSpace (X j)] [MeasurableSpace C]

/-- The distributions of the histories (Proposition 7.45 and eqs. (16), (28) of Chapter 10):
for an initial distribution `q` of `y₀`, Borel transition kernels `t j (dy_{j+1} | y_j, u_j)`
and control kernels `μ n (du_n | y₀, u₀, …, yₙ)` (possibly only universally measurable),
`histLaw q t μ n` is the probability measure on `Hist X C n` characterized on measurable
rectangles by
* `P₀(A × D) = ∫_A μ₀(D | y₀) q(dy₀)`,
* `P_{n+1}(E × A × D) = ∫_E ∫_A μ_{n+1}(D | h, y) t_n(dy | yₙ, uₙ) P_n(dh)`.
Such a measure exists and is unique (Proposition 7.45); the `else 0` branch is never used. -/
noncomputable def histLaw (q : Measure (X 0)) (t : (j : ℕ) → Kernel (X j × C) (X (j + 1)))
    (μ : (n : ℕ) → Obs X C n → Measure C) : (n : ℕ) → Measure (Hist X C n)
  | 0 =>
    if h : ∃ P : Measure (Hist X C 0), IsProbabilityMeasure P ∧
        ∀ (A : Set (X 0)) (D : Set C), MeasurableSet A → MeasurableSet D →
          P {h | h.state ∈ A ∧ h.control ∈ D} = ∫⁻ y in A, μ 0 (Obs.init y) D ∂q
    then h.choose else 0
  | n + 1 =>
    if h : ∃ P : Measure (Hist X C (n + 1)), IsProbabilityMeasure P ∧
        ∀ (E : Set (Hist X C n)) (A : Set (X (n + 1))) (D : Set C),
          MeasurableSet E → MeasurableSet A → MeasurableSet D →
          P {h | h.prefix ∈ E ∧ h.state ∈ A ∧ h.control ∈ D} =
            ∫⁻ h in E, (∫⁻ y in A, μ (n + 1) (h.extend y) D ∂(t n (h.state, h.control)))
              ∂(histLaw q t μ n)
    then h.choose else 0

end BertsekasShreve.ImperfectInfo
