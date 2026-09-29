import Mathlib
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_SetCoverThreshold_SetCover_Complexity

namespace SetCoverThreshold.SetCover

open CookPvsNP

/-- `F` is a 3CNF-B formula (Feige 1998, p. 639, MAX 3SAT-B): every clause has at most three
literals, and every variable occurs in at most `B` clauses. -/
def Is3CNFB (B : ℕ) (F : CNF) : Prop :=
  (∀ C ∈ F, C.length ≤ 3) ∧
    ∀ v : ℕ, (F.filter (fun C => decide (∃ ℓ ∈ C, ℓ.2 = v))).length ≤ B

/-- "At most a `θ`-fraction of the clauses of `F` can be satisfied simultaneously": `F` has at
least one clause, and every assignment satisfies at most `θ · |F|` clauses. -/
def AtMostFracSat (θ : ℝ) (F : CNF) : Prop :=
  0 < F.length ∧
    ∀ τ : ℕ → Bool,
      ((F.filter (fun C => decide (∃ ℓ ∈ C, τ ℓ.2 = ℓ.1))).length : ℝ) ≤ θ * F.length

/-- A 3CNF-5 formula (Feige 1998, p. 640, MAX 3SAT-5) on the variables `0, …, n-1` with `M ≥ 1`
clauses. Clause `c` is `clause c 0 ∨ clause c 1 ∨ clause c 2`; a literal `(b, v)` is the variable
`x_v` if `b = true` and `¬x_v` if `b = false`. Every clause has exactly three literals on three
distinct variables, and every variable appears in exactly five clauses. -/
structure Formula5 where
  /-- number of variables -/
  n : ℕ
  /-- number of clauses -/
  M : ℕ
  M_pos : 0 < M
  /-- the three literals of each clause -/
  clause : Fin M → Fin 3 → Bool × Fin n
  /-- a variable does not appear in a clause more than once -/
  distinct : ∀ c, Function.Injective (fun p => (clause c p).2)
  /-- every variable appears in exactly five clauses -/
  five : ∀ v : Fin n,
    (Finset.univ.filter (fun cp : Fin M × Fin 3 => (clause cp.1 cp.2).2 = v)).card = 5

namespace Formula5

variable (φ : Formula5)

/-- The variable at position `p` of clause `c`. -/
def var (c : Fin φ.M) (p : Fin 3) : Fin φ.n := (φ.clause c p).2

/-- The three bits `b` (the values of the three variables of clause `c`, in position order)
satisfy clause `c`. -/
def ClauseSatBy (c : Fin φ.M) (b : Fin 3 → Bool) : Prop := ∃ p, b p = (φ.clause c p).1

instance (c : Fin φ.M) (b : Fin 3 → Bool) : Decidable (φ.ClauseSatBy c b) := by
  unfold ClauseSatBy; infer_instance

/-- The formula as a `CookPvsNP.CNF` (variable `x_v` becomes the natural number `v`). -/
def toCNF : CNF :=
  List.ofFn fun c : Fin φ.M => List.ofFn fun p : Fin 3 => ((φ.clause c p).1, ((φ.clause c p).2 : ℕ))

end Formula5

/-- Theorem 2.1.1 of Feige 1998 (p. 639; Arora et al. 1992, Papadimitriou–Yannakakis 1991), taken
as a hypothesis: for some bound `B` and some `ε > 0` it is NP-hard to distinguish satisfiable
3CNF-B formulas from 3CNF-B formulas in which at most a `(1 - ε)`-fraction of the clauses can be
satisfied simultaneously. -/
def Thm211 : Prop :=
  ∃ (B : ℕ) (ε : ℝ), 0 < ε ∧
    GapNPHard encodeCNF (fun F => Is3CNFB B F ∧ F.Satisfiable)
      (fun F => Is3CNFB B F ∧ AtMostFracSat (1 - ε) F)

end SetCoverThreshold.SetCover
