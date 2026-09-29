import Mathlib

open MeasureTheory

namespace VectorPayoffs.Convex

/-- Euclidean `N`-space, where the vector payoffs live. -/
abbrev E (N : ℕ) : Type := EuclideanSpace ℝ (Fin N)

/-- Blackwell (1956), §1, p. 1: an `r × s` matrix `M = ‖m(i, j)‖` each element of which is a
probability distribution over a closed bounded convex set `X` in Euclidean `N`-space. -/
structure Game (N r s : ℕ) where
  /-- The closed bounded convex set carrying every payoff distribution. -/
  X : Set (E N)
  isClosed_X : IsClosed X
  isBounded_X : Bornology.IsBounded X
  convex_X : Convex ℝ X
  /-- `m i j` is the payoff distribution when I plays row `i` and II plays column `j`. -/
  m : Fin r → Fin s → Measure (E N)
  isProb : ∀ i j, IsProbabilityMeasure (m i j)
  m_compl_X : ∀ i j, m i j Xᶜ = 0

namespace Game

variable {N r s : ℕ}

/-- §2, p. 3: `m̄(i, j)`, the mean value of the distribution `m(i, j)` (the matrix `M̄`). -/
noncomputable def mbar (G : Game N r s) (i : Fin r) (j : Fin s) : E N :=
  ∫ x, x ∂(G.m i j)

/-- §1, p. 2: the `s × r` matrix `M'`, the transpose of `M` (roles of the players swapped). -/
def transpose (G : Game N r s) : Game N s r where
  X := G.X
  isClosed_X := G.isClosed_X
  isBounded_X := G.isBounded_X
  convex_X := G.convex_X
  m := fun j i => G.m i j
  isProb := fun j i => G.isProb i j
  m_compl_X := fun j i => G.m_compl_X i j

/-- §2, p. 3: for `p ∈ P`, `R(p)` is the convex hull of the `s` points `∑ᵢ pᵢ m̄(i, j)`. -/
noncomputable def R (G : Game N r s) (p : Fin r → ℝ) : Set (E N) :=
  convexHull ℝ (Set.range fun j : Fin s => ∑ i, p i • G.mbar i j)

/-- §3, p. 6 (THEOREM 3): for `q ∈ Q`, `T(q)` is the convex hull of the `r` points
`∑ⱼ qⱼ m̄(i, j)`. -/
noncomputable def T (G : Game N r s) (q : Fin s → ℝ) : Set (E N) :=
  convexHull ℝ (Set.range fun i : Fin r => ∑ j, q j • G.mbar i j)

end Game

/-- §1, pp. 1–2: a strategy for a player with `k` pure actions: for every `n = 0, 1, 2, …` a
function of the `n`-tuple of past outcomes `(x₁, …, xₙ)` with values in the simplex of mixed
actions. Measurability in the history is required so that the play is a well-defined process. -/
structure Strategy (N k : ℕ) where
  toFun : (n : ℕ) → (Fin n → E N) → (Fin k → ℝ)
  mem : ∀ n h, toFun n h ∈ stdSimplex ℝ (Fin k)
  meas : ∀ n, Measurable (toFun n)

/-- The stationary strategy `fₙ ≡ q`. -/
def Strategy.const {N k : ℕ} (q : Fin k → ℝ) (hq : q ∈ stdSimplex ℝ (Fin k)) :
    Strategy N k where
  toFun := fun _ _ => q
  mem := fun _ _ => hq
  meas := fun _ => measurable_const

/-- The average `(1/n) ∑_{k=1}^n x_k` of a history of length `n` (it is `0` for `n = 0`). -/
noncomputable def avgHist {N n : ℕ} (h : Fin n → E N) : E N :=
  (n : ℝ)⁻¹ • ∑ k, h k

/-- The history `(x₁, …, xₙ)` of an outcome process `x`, indexed from `1` (`x 0` is unused). -/
def hist {N : ℕ} {Ω : Type} (x : ℕ → Ω → E N) (n : ℕ) (ω : Ω) : Fin n → E N :=
  fun k => x (k.val + 1) ω

/-- `x̄ₙ = (1/n) ∑_{i=1}^n xᵢ`. -/
noncomputable def avg {N : ℕ} {Ω : Type} (x : ℕ → Ω → E N) (n : ℕ) (ω : Ω) : E N :=
  avgHist (hist x n ω)

namespace Game

variable {N r s : ℕ}

/-- §1, p. 2: `x₁, x₂, …` is the sequence of random outcomes determined by the pair of
strategies `(f, g)` together with `M`: each `xₙ` is measurable, and given `x₁, …, xₙ` the next
outcome `xₙ₊₁` has law `∑ᵢ ∑ⱼ pᵢ qⱼ m(i, j)` with `p = fₙ(x₁, …, xₙ)`, `q = gₙ(x₁, …, xₙ)`
(I and II draw `i` and `j` independently from `p` and `q`, then the outcome is drawn from
`m(i, j)`). -/
def IsPlay (G : Game N r s) (f : Strategy N r) (g : Strategy N s) {Ω : Type}
    [MeasurableSpace Ω] (μ : Measure Ω) (x : ℕ → Ω → E N) : Prop :=
  (∀ n, Measurable (x (n + 1))) ∧
  ∀ (n : ℕ) (B : Set (E N)), MeasurableSet B →
    μ[(x (n + 1) ⁻¹' B).indicator (fun _ => (1 : ℝ)) |
        MeasurableSpace.comap (hist x n) inferInstance]
      =ᵐ[μ] fun ω => ∑ i, ∑ j,
        f.toFun n (hist x n ω) i * g.toFun n (hist x n ω) j * (G.m i j B).toReal

/-- §1, p. 2: `S` is approachable with `f` in `M`: for every `ε > 0` there is an `N₀` such
that, for every strategy `g` of II and every play of `(f, g)`,
`Prob {δₙ ≥ ε for some n ≥ N₀} < ε`, where `δₙ` is the distance from `x̄ₙ` to `S`. -/
def ApproachableWith (G : Game N r s) (S : Set (E N)) (f : Strategy N r) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ (g : Strategy N s) (Ω : Type) [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (x : ℕ → Ω → E N), G.IsPlay f g μ x →
      (μ {ω | ∃ n, N₀ ≤ n ∧ 1 ≤ n ∧
        ENNReal.ofReal ε ≤ Metric.infEDist (avg x n ω) S}).toReal < ε

/-- §1, p. 2: `S` is excludable with `g` in `M`: there is `d > 0` such that for every `ε > 0`
there is an `N₀` such that, for every strategy `f` of I and every play of `(f, g)`,
`Prob {δₙ ≥ d for all n ≥ N₀} > 1 - ε`. -/
def ExcludableWith (G : Game N r s) (S : Set (E N)) (g : Strategy N s) : Prop :=
  ∃ d : ℝ, 0 < d ∧ ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ (f : Strategy N r) (Ω : Type)
    [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (x : ℕ → Ω → E N),
      G.IsPlay f g μ x →
        1 - ε < (μ {ω | ∀ n, N₀ ≤ n → 1 ≤ n →
          ENNReal.ofReal d ≤ Metric.infEDist (avg x n ω) S}).toReal

/-- `S` is approachable in `M`: approachable with some strategy of I. -/
def ApproachableIn (G : Game N r s) (S : Set (E N)) : Prop :=
  ∃ f : Strategy N r, G.ApproachableWith S f

/-- `S` is excludable in `M`: excludable with some strategy of II. -/
def ExcludableIn (G : Game N r s) (S : Set (E N)) : Prop :=
  ∃ g : Strategy N s, G.ExcludableWith S g

/-- THEOREM 1's condition at a point `x ∉ S` with mixed action `p`: some point `y` of `S`
closest to `x` is such that the hyperplane through `y` perpendicular to `xy` (weakly)
separates `x` from `R(p)`, i.e. `⟪x - y, w - y⟫ ≤ 0` for every `w ∈ R(p)`. -/
def BlackwellCondition (G : Game N r s) (S : Set (E N)) (p : Fin r → ℝ) (x : E N) : Prop :=
  ∃ y ∈ S, (∀ z ∈ S, dist x y ≤ dist x z) ∧ ∀ w ∈ G.R p, inner ℝ (x - y) (w - y) ≤ 0

end Game

end VectorPayoffs.Convex
