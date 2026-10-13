import Mathlib
import Definitions.Def_agt_social

namespace StrategyProofArrow.Dictatorship

open AGT

variable {ι A : Type*}

/-- The range `T_p` of a strict voting procedure (Satterthwaite, p. 6 and pp. 8–9): the set of
alternatives chosen at some strict ballot set. Ballot sets are profiles of strict total orders
(`AGT.IsPrefProfile`), the paper's `ρ^n_m`; values of `f` at other relation profiles are ignored. -/
def range (f : (ι → A → A → Prop) → A) : Set A :=
  {x | ∃ P : ι → A → A → Prop, IsPrefProfile P ∧ f P = x}

/-- `x` is the `r`-maximal element of `T` (`Ψ_T(r) = {x}` for a strong order `r`, p. 9):
`x ∈ T` and `r` ranks `x` strictly above every other element of `T`. Here `r a b` reads
"`a` strictly above `b`". -/
def IsTopIn (r : A → A → Prop) (T : Set A) (x : A) : Prop :=
  x ∈ T ∧ ∀ y ∈ T, y ≠ x → r x y

/-- A strict voting procedure is **dictatorial** (p. 10) if some individual `i` exists such that,
at every strict ballot set `P`, the chosen alternative is `i`'s most preferred element of the range
`T_p` (the paper's `v^{nm}(B) = f^i_T(B)`). -/
def Dictatorial (f : (ι → A → A → Prop) → A) : Prop :=
  ∃ i : ι, ∀ P : ι → A → A → Prop, IsPrefProfile P → IsTopIn (P i) (range f) (f P)

/-- **Fully dictatorial** (p. 10): dictatorial with range the whole alternative set,
`T_p ≡ S_m`. -/
def FullyDictatorial (f : (ι → A → A → Prop) → A) : Prop :=
  range f = Set.univ ∧ Dictatorial f

/-- **Partially dictatorial** (p. 10): dictatorial with range a proper subset of the alternative
set, `T_p ⊂⊂ S_m`. -/
def PartiallyDictatorial (f : (ι → A → A → Prop) → A) : Prop :=
  range f ≠ Set.univ ∧ Dictatorial f

/-- **Condition U** (p. 13): at every strict ballot set at which all individuals have the same
most preferred element `x` of the range `T = T_p`, the procedure chooses `x`. -/
def ConditionU (f : (ι → A → A → Prop) → A) : Prop :=
  ∀ P : ι → A → A → Prop, IsPrefProfile P →
    ∀ x : A, (∀ i, IsTopIn (P i) (range f) x) → f P = x

/-- **Weak alternative-excluding** (p. 13): some alternative is chosen at no strict ballot set. -/
def WeakAltExcluding (f : (ι → A → A → Prop) → A) : Prop :=
  ∃ x : A, ∀ P : ι → A → A → Prop, IsPrefProfile P → f P ≠ x

/-- **Strong alternative-excluding** (p. 13): weak alternative-excluding and Condition U. -/
def StrongAltExcluding (f : (ι → A → A → Prop) → A) : Prop :=
  WeakAltExcluding f ∧ ConditionU f

/-- `θ_T(r) = θ_T(s)` (p. 9): the two strict ballots order the elements of `T` alike. -/
def AgreeOn (T : Set A) (r s : A → A → Prop) : Prop :=
  ∀ x ∈ T, ∀ y ∈ T, (r x y ↔ s x y)

/-- The `n`-voter section of an `(n+1)`-voter procedure (display (6), pp. 16–17): voters are
`Option ι`, `none` is individual `n+1`, and the section for voter `n+1`'s ballot `b` is the
procedure `B ↦ v^{n+1}(B, b)` of the remaining voters. -/
def sectionAt (f : (Option ι → A → A → Prop) → A) (b : A → A → Prop) :
    (ι → A → A → Prop) → A :=
  fun Q => f (fun o => o.elim b Q)

end StrategyProofArrow.Dictatorship
