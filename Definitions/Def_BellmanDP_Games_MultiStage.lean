import Mathlib
import Definitions.Def_BellmanDP_Games_MinMax

namespace BellmanDP.Games

open MeasureTheory

/-- Real `n`-dimensional vectors, the states `P`, `P'` and choice vectors `u`, `v` of Ch. X,
§ 12, p. 295. -/
abbrev Vec (n : ℕ) : Type := Fin n → ℝ

/-- Ch. X, § 12, Eq. (12.1), p. 296: `‖P‖ = Σ_{i=1}^n |P_i|`. -/
def l1norm {n : ℕ} (P : Vec n) : ℝ :=
  ∑ i, |P i|

/-- The data of the general multi-stage game of Ch. X, § 12, p. 295–296.

* `D`, `D'`: the regions in which the state vectors `P ∈ ℝⁿ`, `P' ∈ ℝ^{n'}` lie;
* `S P P' ⊆ ℝ^m`, `S' P P' ⊆ ℝ^{m'}`: the choice domains of `A` and `B` in state `(P, P')`,
  nonempty compact sets;
* `R u v`: the return to `A` of a single stage when `A` chooses `u` and `B` chooses `v`;
* `h P P' u v`: the multiplier in front of the continuation return;
* `T P P' u v`, `T' P P' u v`: the new state vectors. -/
structure GameData (n n' m m' : ℕ) where
  D : Set (Vec n)
  D' : Set (Vec n')
  S : Vec n → Vec n' → TopologicalSpace.NonemptyCompacts (Vec m)
  S' : Vec n → Vec n' → TopologicalSpace.NonemptyCompacts (Vec m')
  R : Vec m → Vec m' → ℝ
  h : Vec n → Vec n' → Vec m → Vec m' → ℝ
  T : Vec n → Vec n' → Vec m → Vec m' → Vec n
  T' : Vec n → Vec n' → Vec m → Vec m' → Vec n'

variable {n n' m m' : ℕ}

/-- The mixed strategies on a choice domain `S`: probability measures (distribution functions
`G(u)` in Bellman's notation) giving full mass to `S`. -/
def MixedStrategies {m : ℕ} (S : Set (Vec m)) : Set (Measure (Vec m)) :=
  {G | IsProbabilityMeasure G ∧ G Sᶜ = 0}

/-- The expected payoff `∫∫ K(u, v) dG(u) dG'(v)` of the kernel `K` under the mixed strategies
`G`, `G'`. -/
noncomputable def expectedPayoff (K : Vec m → Vec m' → ℝ) (G : Measure (Vec m))
    (G' : Measure (Vec m')) : ℝ :=
  ∫ u, ∫ v, K u v ∂G' ∂G

/-- The integrand of Ch. X, Eq. (12.2), p. 296: `R(u, v) + h(P, P'; u, v) f(T, T')` with
`T = T(P, P'; u, v)`, `T' = T'(P, P'; u, v)`. -/
def stageKernel (g : GameData n n' m m') (f : Vec n → Vec n' → ℝ) (P : Vec n) (P' : Vec n')
    (u : Vec m) (v : Vec m') : ℝ :=
  g.R u v + g.h P P' u v * f (g.T P P' u v) (g.T' P P' u v)

/-- "`Max_G Min_{G'} ∫∫ K dG dG' = Min_{G'} Max_G ∫∫ K dG dG' = x`" in state `(P, P')`: the
one-stage game with kernel `K`, played with mixed strategies on the choice domains `S(P, P')`,
`S'(P, P')`, has value `x` (all extrema attained). -/
def ValueAt (g : GameData n n' m m') (K : Vec m → Vec m' → ℝ) (P : Vec n) (P' : Vec n')
    (x : ℝ) : Prop :=
  IsMaxMinMinMaxValue (fun G G' => expectedPayoff K G G')
    (MixedStrategies (g.S P P' : Set (Vec m))) (MixedStrategies (g.S' P P' : Set (Vec m'))) x

/-- Ch. X, Eqs. (12.2)–(12.3), p. 296: `f` solves
`f(P, P') = Max_G Min_{G'} T(P, P'; f; G, G') = Min_{G'} Max_G T(P, P'; f; G, G')`
for every `P ∈ D`, `P' ∈ D'`. -/
def IsGameSolution (g : GameData n n' m m') (f : Vec n → Vec n' → ℝ) : Prop :=
  ∀ P ∈ g.D, ∀ P' ∈ g.D', ValueAt g (stageKernel g f P P') P P' (f P P')

/-- The class of Ch. X, Theorem 1, p. 297: functions continuous for all `P ∈ D`, `P' ∈ D'` that
vanish when `P` and `P'` are both null vectors. -/
def InSolutionClass (g : GameData n n' m m') (f : Vec n → Vec n' → ℝ) : Prop :=
  ContinuousOn (fun z : Vec n × Vec n' => f z.1 z.2) (g.D ×ˢ g.D') ∧ f 0 0 = 0

/-- The bounded region `{(P, P') : P ∈ D, P' ∈ D', ‖P‖ + ‖P'‖ ≤ c}`. -/
def region (g : GameData n n' m m') (c : ℝ) : Set (Vec n × Vec n') :=
  {z | z.1 ∈ g.D ∧ z.2 ∈ g.D' ∧ l1norm z.1 + l1norm z.2 ≤ c}

/-- The recurrence `f_{N+1}(P, P') = Max_G Min_{G'} T(P, P'; f_N; G, G') = Min_{G'} Max_G T(…)`
(Ch. X, Eq. (12.5), p. 297 and Theorem 3, Eq. (15.1), p. 300) on `D × D'`. -/
def IsIterSeq (g : GameData n n' m m') (fs : ℕ → Vec n → Vec n' → ℝ) : Prop :=
  ∀ N : ℕ, ∀ P ∈ g.D, ∀ P' ∈ g.D', ValueAt g (stageKernel g (fs N) P P') P P' (fs (N + 1) P P')

/-- Ch. X, Theorem 1, hypotheses (4a)–(4e), pp. 296–297, with the constant `k` of (4c).

"Vary continuously" in (4b) is read as continuity of `(P, P') ↦ S(P, P')` on `D × D'` for the
Hausdorff metric on nonempty compact sets. The maximum `w(c)` of (4d) is expressed through a
majorant `W`: `Σ_{n ≥ 1} w(kⁿ c) < ∞` for every `c > 0` holds exactly when some `W ≥ w` has
`Σ_{n ≥ 1} W(kⁿ c) < ∞` for every `c > 0`. -/
structure GameHyp (g : GameData n n' m m') (k : ℝ) : Prop where
  /-- § 12: `D` contains the origin. -/
  zero_mem_D : (0 : Vec n) ∈ g.D
  /-- § 12: `D'` contains the origin. -/
  zero_mem_D' : (0 : Vec n') ∈ g.D'
  /-- § 12: the transformed vector `T` lies in `D`. -/
  T_mem : ∀ P ∈ g.D, ∀ P' ∈ g.D', ∀ u ∈ (g.S P P' : Set (Vec m)),
    ∀ v ∈ (g.S' P P' : Set (Vec m')), g.T P P' u v ∈ g.D
  /-- § 12: the transformed vector `T'` lies in `D'`. -/
  T'_mem : ∀ P ∈ g.D, ∀ P' ∈ g.D', ∀ u ∈ (g.S P P' : Set (Vec m)),
    ∀ v ∈ (g.S' P P' : Set (Vec m')), g.T' P P' u v ∈ g.D'
  /-- (4a) `R(u, v)` is continuous. -/
  cont_R : Continuous (fun z : Vec m × Vec m' => g.R z.1 z.2)
  /-- (4a) `h(P, P'; u, v)` is continuous in all variables. -/
  cont_h : ContinuousOn (fun z : (Vec n × Vec n') × (Vec m × Vec m') => g.h z.1.1 z.1.2 z.2.1 z.2.2)
    ((g.D ×ˢ g.D') ×ˢ Set.univ)
  /-- (4a) `T(P, P'; u, v)` is continuous in all variables. -/
  cont_T : ContinuousOn (fun z : (Vec n × Vec n') × (Vec m × Vec m') => g.T z.1.1 z.1.2 z.2.1 z.2.2)
    ((g.D ×ˢ g.D') ×ˢ Set.univ)
  /-- (4a) `T'(P, P'; u, v)` is continuous in all variables. -/
  cont_T' : ContinuousOn
    (fun z : (Vec n × Vec n') × (Vec m × Vec m') => g.T' z.1.1 z.1.2 z.2.1 z.2.2)
    ((g.D ×ˢ g.D') ×ˢ Set.univ)
  /-- (4b) `S(P, P')` varies continuously with `P`, `P'`. -/
  cont_S : ContinuousOn (fun z : Vec n × Vec n' => g.S z.1 z.2) (g.D ×ˢ g.D')
  /-- (4b) `S'(P, P')` varies continuously with `P`, `P'`. -/
  cont_S' : ContinuousOn (fun z : Vec n × Vec n' => g.S' z.1 z.2) (g.D ×ˢ g.D')
  /-- (4c) `k ≥ 0` (forced by (4c) as soon as `D × D'` has a nonzero point). -/
  k_nonneg : 0 ≤ k
  /-- (4c) `k < 1`. -/
  k_lt_one : k < 1
  /-- (4c) `‖T‖ + ‖T'‖ ≤ k (‖P‖ + ‖P'‖)` for all `u ∈ S`, `v ∈ S'`. -/
  shrinking : ∀ P ∈ g.D, ∀ P' ∈ g.D', ∀ u ∈ (g.S P P' : Set (Vec m)),
    ∀ v ∈ (g.S' P P' : Set (Vec m')),
      l1norm (g.T P P' u v) + l1norm (g.T' P P' u v) ≤ k * (l1norm P + l1norm P')
  /-- (4d) `Σ_{n=1}^∞ w(kⁿ c) < ∞` for all `c > 0`, where
  `w(c) = Max_{‖P‖ + ‖P'‖ ≤ c} Max_{u ∈ S, v ∈ S'} |R(u, v)|`. -/
  summable_w : ∃ W : ℝ → ℝ,
    (∀ c : ℝ, ∀ P ∈ g.D, ∀ P' ∈ g.D', l1norm P + l1norm P' ≤ c →
      ∀ u ∈ (g.S P P' : Set (Vec m)), ∀ v ∈ (g.S' P P' : Set (Vec m')), |g.R u v| ≤ W c) ∧
    ∀ c : ℝ, 0 < c → Summable (fun j : ℕ => W (k ^ (j + 1) * c))
  /-- (4e) `Max_{u, v, P, P'} |h(u, v, P, P')| ≤ 1`. -/
  h_le_one : ∀ P ∈ g.D, ∀ P' ∈ g.D', ∀ u ∈ (g.S P P' : Set (Vec m)),
    ∀ v ∈ (g.S' P P' : Set (Vec m')), |g.h P P' u v| ≤ 1

end BellmanDP.Games
