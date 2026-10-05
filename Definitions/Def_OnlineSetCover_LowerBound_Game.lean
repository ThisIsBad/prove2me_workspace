import Mathlib

namespace OnlineSetCover.LowerBound

/-- A deterministic online algorithm for the unweighted online set cover problem on a ground
set `X` (Alon et al. 2009, §1, pp. 361–362). When an element `x` arrives, the algorithm sees the
list `h` of the elements that arrived before it (in arrival order, oldest first) and the new
element `x`, and returns the finite family `A h x` of sets it adds to its collection at this
step (any number of sets, possibly none). The instance itself (the ground set and the family)
is fixed in advance and known to the algorithm. Being deterministic, its choices are a function
of the arrivals alone. -/
abbrev OnlineAlg (X : Type*) := List X → X → Finset (Finset X)

variable {X : Type*} [DecidableEq X]

/-- `chosenFrom A h σ`: the sets added by `A` while the elements of `σ` arrive one by one (in
order), after the elements of `h` have already arrived. -/
def chosenFrom (A : OnlineAlg X) : List X → List X → Finset (Finset X)
  | _, [] => ∅
  | h, x :: rest => A h x ∪ chosenFrom A (h ++ [x]) rest

/-- `chosen A σ`: the collection `𝒞` of sets chosen by `A` (sets are never removed) after the
arrival sequence `σ` (oldest first). -/
def chosen (A : OnlineAlg X) (σ : List X) : Finset (Finset X) :=
  chosenFrom A [] σ

/-- The cost of `A` on the arrival sequence `σ` in the unweighted problem: the number of
distinct sets it has chosen. -/
def cost (A : OnlineAlg X) (σ : List X) : ℕ :=
  (chosen A σ).card

/-- `A` is a valid online algorithm for the family `𝓕`: it only ever adds members of `𝓕`, and
after each arrival `x` (whatever the earlier arrivals `h`), if `x` lies in some member of `𝓕`
then `x` lies in some set chosen so far. -/
def IsValid (𝓕 : Finset (Finset X)) (A : OnlineAlg X) : Prop :=
  ∀ (h : List X) (x : X),
    A h x ⊆ 𝓕 ∧ ((∃ S ∈ 𝓕, x ∈ S) → ∃ S ∈ chosen A (h ++ [x]), x ∈ S)

/-- `C` is an offline cover of the arrivals `σ` by the family `𝓕`: `C` is a subfamily of `𝓕`
and every arrived element lies in some member of `C`. The offline optimum `OPT(σ)` is the least
cardinality of such a `C`. -/
def IsCoverOf (𝓕 C : Finset (Finset X)) (σ : List X) : Prop :=
  C ⊆ 𝓕 ∧ ∀ x ∈ σ, ∃ S ∈ C, x ∈ S

end OnlineSetCover.LowerBound
