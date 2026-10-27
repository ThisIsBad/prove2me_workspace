import Mathlib
import Definitions.Def_CookPvsNP_defs

namespace SetCoverThreshold.SetCover

/-- A set-cover instance (Feige 1998, p. 634): the points `Fin n` and a list of subsets
`S_1, …, S_s`. -/
structure SCInstance where
  n : ℕ
  sets : List (Finset (Fin n))

namespace SCInstance

variable (I : SCInstance)

/-- A cover: a set of indices of the list whose subsets together contain every point. -/
def IsCover (C : Finset (Fin I.sets.length)) : Prop :=
  ∀ x : Fin I.n, ∃ i ∈ C, x ∈ I.sets.get i

/-- The instance has a cover: every point lies in some subset. -/
def Coverable : Prop := ∀ x : Fin I.n, ∃ S ∈ I.sets, x ∈ S

/-- String encoding over `Option Bool`: `n` in unary (`some true`, `n` times), a separator
`none`, then each subset as its characteristic bit-vector of length `n` followed by `none`. -/
def encode : List (Option Bool) :=
  List.replicate I.n (some true) ++ none ::
    I.sets.flatMap fun S => List.ofFn (fun x : Fin I.n => some (decide (x ∈ S))) ++ [none]

end SCInstance

/-- A deterministic polynomial-time algorithm approximates set cover within `ρ(n)`
(Feige 1998, p. 634), in value form: there are a polynomial-time computable
`A : List (Option Bool) → List Unit` and a threshold `n₀` such that on every coverable instance
with `n ≥ n₀` points the output length `v` satisfies: some cover has at most `v` subsets, and
`v ≤ ρ(n) · |C|` for every cover `C`. -/
def ApproximableWithin (ρ : ℕ → ℝ) : Prop :=
  ∃ A : List (Option Bool) → List Unit, CookPvsNP.PolyTimeComputable A ∧
    ∃ n₀ : ℕ, ∀ I : SCInstance, n₀ ≤ I.n → I.Coverable →
      (∃ C, I.IsCover C ∧ C.card ≤ (A I.encode).length) ∧
        ∀ C, I.IsCover C → ((A I.encode).length : ℝ) ≤ ρ I.n * C.card

end SetCoverThreshold.SetCover
