import Mathlib
import Definitions.Def_OnlineRandomization_Tightness_Model

namespace OnlineRandomization.Tightness

open MeasureTheory

/-- p. 12: the request set and the answer set are both `Fin t × Bool`, a set of `2t` elements
in the `t` disjoint pairs `{(i, false), (i, true)}`; the two elements of a pair are *mates*. -/
def mate {t : ℕ} (x : Fin t × Bool) : Fin t × Bool :=
  (x.1, !x.2)

/-- p. 12: the cost determined by the first answer `a₁` and the second request `r₂`:
`1` if `a₁ = r₂`, `M` if `a₁` is the mate of `r₂`, and `m` otherwise. -/
def pairCost {t : ℕ} (m M : ℝ) (a₁ r₂ : Fin t × Bool) : ℝ :=
  if a₁ = r₂ then 1 else if a₁ = mate r₂ then M else m

/-- p. 12: the cost `f_n(r, a)` of the mates game. For `n ≥ 2` it is `pairCost m M a₁ r₂`
(the page). The page leaves `f_0` and `f_1` undefined; here `f_0 = 0` (no request, no cost)
and `f_1 ≡ 1` (a play with a single request costs `1`, for the algorithm and for the
adversary alike). The last clause (at least two requests and no answer) concerns lists of
different lengths and is never used. -/
def matesCost {t : ℕ} (m M : ℝ) : List (Fin t × Bool) → List (Fin t × Bool) → ℝ
  | [], _ => 0
  | [_], _ => 1
  | _ :: r₂ :: _, a₁ :: _ => pairCost m M a₁ r₂
  | _ :: _ :: _, [] => 0

/-- p. 12: the mates request-answer game with parameters `t`, `m`, `M`. -/
def matesGame (t : ℕ) (m M : ℝ) : Game (Fin t × Bool) (Fin t × Bool) :=
  ⟨matesCost m M⟩

/-- p. 12: the algorithm `G`, which draws its first answer `a₁` uniformly from `A`; its other
answers are irrelevant, and here every answer equals `a₁`. The coin space is `A = Fin t × Bool`
itself with the uniform probability measure (its σ-algebra is the discrete one), and on the
coin `ω` the algorithm answers `ω` to every request. -/
noncomputable def unifAlg (t : ℕ) [NeZero t] :
    RandAlg (Fin t × Bool) (Fin t × Bool) (Fin t × Bool) where
  μ := (PMF.uniformOfFintype (Fin t × Bool)).toMeasure
  isProb := inferInstance
  alg ω := fun _ => ω
  meas _ _ := MeasurableSet.of_discrete

/-- p. 12: the parameter `m = m(t)`, the closed-form solution for `m` of the simultaneous
equations `β = ((2t − 2)m + M + 1)/(2t)`, `α = (1 + (2t − 1)M)/(2 + (2t − 2)m)`:
`m(t) = (1 + (2t − 1)(2tβ − 1) − 2α) / ((2t − 2)(α + 2t − 1))`. Only `t ≥ 2` is used
(at `t = 1` the denominator vanishes and Lean's division returns `0`). -/
noncomputable def paramSmall (α β : ℝ) (t : ℕ) : ℝ :=
  (1 + (2 * (t : ℝ) - 1) * (2 * (t : ℝ) * β - 1) - 2 * α) /
    ((2 * (t : ℝ) - 2) * (α + 2 * (t : ℝ) - 1))

/-- p. 12: the parameter `M = M(t)`, the closed-form solution for `M` of the same equations:
`M(t) = (2tαβ + α − 1) / (α + 2t − 1)`. -/
noncomputable def paramLarge (α β : ℝ) (t : ℕ) : ℝ :=
  (2 * (t : ℝ) * α * β + α - 1) / (α + 2 * (t : ℝ) - 1)

end OnlineRandomization.Tightness
