import Mathlib
import Definitions.Def_CookPvsNP_defs

namespace SetCoverThreshold.MaxCover

open CookPvsNP

/-- **MAX 3SAT-B instances** (Feige 1998, p. 639, §2.1 "Input"): every clause of the CNF formula
`F` contains at most three literals, and every variable appears in at most `B` clauses. -/
def Is3CNFB (B : ℕ) (F : CNF) : Prop :=
  (∀ C ∈ F, C.length ≤ 3) ∧
    ∀ v : ℕ, (F.filter (fun C => decide (∃ l ∈ C, l.2 = v))).length ≤ B

/-- **MAX 3SAT-5 instances** (Feige 1998, p. 640, §2.1 "Input"): every clause contains exactly
three literals, a variable does not appear in a clause more than once, and every variable that
occurs in `F` appears in exactly five clauses. -/
def Is3CNF5 (F : CNF) : Prop :=
  (∀ C ∈ F, C.length = 3 ∧ (C.map Prod.snd).Nodup) ∧
    ∀ v : ℕ, (∃ C ∈ F, ∃ l ∈ C, l.2 = v) →
      (F.filter (fun C => decide (∃ l ∈ C, l.2 = v))).length = 5

/-- **At most a `θ`-fraction of the clauses can be satisfied simultaneously**: under every
assignment `τ` of truth values to the variables, the number of clauses of `F` containing a true
literal is at most `θ · |F|` (clauses counted with multiplicity). -/
def AtMostFracSat (θ : ℝ) (F : CNF) : Prop :=
  ∀ τ : ℕ → Bool, ((F.filter (fun C => decide (∃ l ∈ C, τ l.2 = l.1))).length : ℝ) ≤ θ * F.length

/-- **Gap (promise) NP-hardness**: "it is NP-hard to distinguish between `Yes` and `No`
instances". Every NP language `L'` over any finite nonempty alphabet is mapped by a function `f`
(whose composition with the encoding `enc` is polynomial-time computable) to `Yes`-instances on
members of `L'` and to `No`-instances on non-members. -/
def GapNPHard {α Sym : Type} (enc : α → List Sym) (Yes No : α → Prop) : Prop :=
  ∀ (Sym' : Type) [Fintype Sym'] [Nonempty Sym'] (L' : Lang Sym'), L' ∈ NP Sym' →
    ∃ f : List Sym' → α, PolyTimeComputable (fun x => enc (f x)) ∧
      ∀ x, (x ∈ L' → Yes (f x)) ∧ (x ∉ L' → No (f x))

/-- **Theorem 2.1.1 (cited, p. 639), as a named hypothesis.** For some bound `B` and some
`ε > 0` it is NP-hard to distinguish satisfiable 3CNF-B formulas from 3CNF-B formulas in which at
most a `(1 − ε)`-fraction of the clauses can be satisfied simultaneously. The latter formulas have
at least one clause: the empty formula is satisfiable, so without `F ≠ []` it would be a member of
both classes and the constant reduction `x ↦ []` would witness the gap. -/
def Thm211 : Prop :=
  ∃ (B : ℕ) (ε : ℝ), 0 < ε ∧
    GapNPHard encodeCNF (fun F => Is3CNFB B F ∧ F.Satisfiable)
      (fun F => Is3CNFB B F ∧ F ≠ [] ∧ AtMostFracSat (1 - ε) F)

/-- A **3CNF-5 formula** with its clauses indexed: `M` clauses, clause `c` having literals
`clause c 0, clause c 1, clause c 2` over three distinct variables, and every variable that occurs
occurring in exactly five clauses. -/
structure Formula5 where
  /-- The number of clauses. -/
  M : ℕ
  /-- The three literals of each clause. -/
  clause : Fin M → Fin 3 → Literal
  /-- A variable does not appear in a clause more than once. -/
  distinct_vars : ∀ c, Function.Injective (fun p => (clause c p).2)
  /-- Every variable that occurs appears in exactly five clauses. -/
  five : ∀ v : ℕ, (∃ c p, (clause c p).2 = v) →
    (Finset.univ.filter (fun c => ∃ p, (clause c p).2 = v)).card = 5

namespace Formula5

/-- The variable at position `p` of clause `c`. -/
def var (φ : Formula5) (c : Fin φ.M) (p : Fin 3) : ℕ := (φ.clause c p).2

/-- A local assignment `b` of the three positions of clause `c` satisfies that clause. -/
def LocalSat (φ : Formula5) (c : Fin φ.M) (b : Fin 3 → Bool) : Prop :=
  ∃ p, b p = (φ.clause c p).1

instance (φ : Formula5) (c : Fin φ.M) : DecidablePred (φ.LocalSat c) := by
  intro b; unfold LocalSat; infer_instance

/-- The formula as a `CookPvsNP.CNF`: the list of its clauses, each the list of its three
literals. -/
def toCNF (φ : Formula5) : CNF := List.ofFn (fun c => List.ofFn (φ.clause c))

end Formula5

end SetCoverThreshold.MaxCover
