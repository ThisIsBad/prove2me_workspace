import Mathlib
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_SetCoverThreshold_SetCover_Formula

namespace SetCoverThreshold.SetCover

namespace Formula5

variable (φ : Formula5)

/-! ### The clause–variable game and its `ℓ`-fold parallel repetition (Feige 1998, §2.2) -/

/-- A random string of the verifier for `ℓ` repetitions: for each coordinate `j`, a clause and
the position of the distinguished variable in it. There are `(3M)^ℓ` of them. -/
abbrev RandomString (ℓ : ℕ) : Type := Fin ℓ → Fin φ.M × Fin 3

/-- The `ℓ` clauses selected by a random string (the question to the first prover). -/
def clausesOf {ℓ : ℕ} (r : φ.RandomString ℓ) : Fin ℓ → Fin φ.M := fun j => (r j).1

/-- The `ℓ` distinguished variables selected by a random string (the question to the second
prover). -/
def distVars {ℓ : ℕ} (r : φ.RandomString ℓ) : Fin ℓ → Fin φ.n :=
  fun j => φ.var (r j).1 (r j).2

/-- A strategy of the first prover: to the `ℓ` clauses it answers three bits per clause (an
assignment to the three variables of that clause, in position order). -/
abbrev Prover1Strategy (ℓ : ℕ) : Type := (Fin ℓ → Fin φ.M) → Fin ℓ → Fin 3 → Bool

/-- A strategy of the second prover: to the `ℓ` variables it answers one bit per variable. -/
abbrev Prover2Strategy (ℓ : ℕ) : Type := (Fin ℓ → Fin φ.n) → Fin ℓ → Bool

/-- The verifier of the `ℓ`-fold repeated two-prover system accepts on random string `r`: on
every coordinate, the first prover's bits satisfy the clause (clause check) and agree with the
second prover's bit on the distinguished variable (consistency check). -/
def TwoProverAccepts {ℓ : ℕ} (P₁ : φ.Prover1Strategy ℓ) (P₂ : φ.Prover2Strategy ℓ)
    (r : φ.RandomString ℓ) : Prop :=
  ∀ j, φ.ClauseSatBy (r j).1 (P₁ (φ.clausesOf r) j) ∧
    P₁ (φ.clausesOf r) j (r j).2 = P₂ (φ.distVars r) j

instance {ℓ : ℕ} (P₁ : φ.Prover1Strategy ℓ) (P₂ : φ.Prover2Strategy ℓ) (r : φ.RandomString ℓ) :
    Decidable (φ.TwoProverAccepts P₁ P₂ r) := by
  unfold TwoProverAccepts; infer_instance

/-- Acceptance probability of the `ℓ`-fold two-prover system: the fraction of the `(3M)^ℓ`
random strings on which the verifier accepts. -/
noncomputable def twoProverAcceptFrac (ℓ : ℕ) (P₁ : φ.Prover1Strategy ℓ) (P₂ : φ.Prover2Strategy ℓ) : ℝ :=
  ((Finset.univ.filter (fun r : φ.RandomString ℓ => φ.TwoProverAccepts P₁ P₂ r)).card : ℝ) /
    Fintype.card (φ.RandomString ℓ)

end Formula5

/-- The consequence of Raz's parallel repetition theorem (Feige 1998, Theorem 2.2.2, p. 642) for
the two-prover system of §2.2, taken as a hypothesis: for every `ε > 0` there is `c > 0` such
that for every 3CNF-5 formula in which at most a `(1 - ε)`-fraction of the clauses are
simultaneously satisfiable, every `ℓ` and every pair of strategies, the `ℓ`-fold repeated system
accepts with probability at most `2^{-cℓ}`. -/
def RazRepetition : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ c : ℝ, 0 < c ∧
    ∀ φ : Formula5, AtMostFracSat (1 - ε) φ.toCNF →
      ∀ (ℓ : ℕ) (P₁ : φ.Prover1Strategy ℓ) (P₂ : φ.Prover2Strategy ℓ),
        φ.twoProverAcceptFrac ℓ P₁ P₂ ≤ (2 : ℝ) ^ (-(c * ℓ))

/-! ### The `k`-prover proof system (Feige 1998, §2.3) -/

/-- The binary code of §2.3: `k` code words of length `ℓ`, each of weight `ℓ/2`
(`2 · weight = ℓ`), with Hamming distance at least `ℓ/3` between any two code words
(`3 · distance ≥ ℓ`). -/
def IsCode (ℓ k : ℕ) (code : Fin k → Fin ℓ → Bool) : Prop :=
  (∀ i, 2 * (Finset.univ.filter (fun j => code i j = true)).card = ℓ) ∧
    ∀ i i', i ≠ i' → ℓ ≤ 3 * hammingDist (code i) (code i')

namespace Formula5

variable (φ : Formula5)

/-- A question coordinate: a clause (`Sum.inl`) or a variable (`Sum.inr`). -/
abbrev QCoord : Type := Fin φ.M ⊕ Fin φ.n

/-- The question to prover `P_i` on random string `r`: on coordinate `j` it receives the clause
`C_j` if bit `j` of its code word is `1`, and the distinguished variable `x_j` if it is `0`. -/
def question {ℓ k : ℕ} (code : Fin k → Fin ℓ → Bool) (r : φ.RandomString ℓ) (i : Fin k) :
    Fin ℓ → φ.QCoord :=
  fun j => if code i j then Sum.inl (r j).1 else Sum.inr (φ.var (r j).1 (r j).2)

/-- Canonical answer bits on one coordinate. On a clause coordinate: three bits (values of the
clause's three variables, in position order) that satisfy the clause. On a variable coordinate:
one bit, stored in position `0` (positions `1, 2` are `false`). -/
def CoordCanonical : φ.QCoord → (Fin 3 → Bool) → Prop
  | Sum.inl c, b => φ.ClauseSatBy c b
  | Sum.inr _, b => b 1 = false ∧ b 2 = false

instance (x : φ.QCoord) (b : Fin 3 → Bool) : Decidable (φ.CoordCanonical x b) := by
  cases x <;> unfold CoordCanonical <;> infer_instance

/-- The canonical answers to a question `q`. -/
def Answer {ℓ : ℕ} (q : Fin ℓ → φ.QCoord) : Type :=
  { a : Fin ℓ → Fin 3 → Bool // ∀ j, φ.CoordCanonical (q j) (a j) }

instance {ℓ : ℕ} (q : Fin ℓ → φ.QCoord) : Fintype (φ.Answer q) := by
  unfold Answer; infer_instance

instance {ℓ : ℕ} (q : Fin ℓ → φ.QCoord) : DecidableEq (φ.Answer q) := by
  unfold Answer; infer_instance

/-- A (deterministic) strategy of the `k` provers: prover `i` answers each question with a
canonical answer. -/
abbrev KStrategy (ℓ k : ℕ) : Type := (i : Fin k) → (q : Fin ℓ → φ.QCoord) → φ.Answer q

/-- The assignment to the sequence of distinguished variables of `r` that answer `a` of prover
`i` induces: on a clause coordinate, the bit at the distinguished position; on a variable
coordinate, the bit itself. -/
def inducedAssignment {ℓ k : ℕ} (code : Fin k → Fin ℓ → Bool) (r : φ.RandomString ℓ)
    (i : Fin k) (a : Fin ℓ → Fin 3 → Bool) : Fin ℓ → Bool :=
  fun j => if code i j then a j (r j).2 else a j 0

/-- The answers of provers `i` and `i'` on random string `r` are consistent: they induce the
same assignment to the distinguished variables. -/
def Consistent {ℓ k : ℕ} (code : Fin k → Fin ℓ → Bool) (A : φ.KStrategy ℓ k)
    (r : φ.RandomString ℓ) (i i' : Fin k) : Prop :=
  φ.inducedAssignment code r i (A i (φ.question code r i)).1 =
    φ.inducedAssignment code r i' (A i' (φ.question code r i')).1

/-- Weak acceptance predicate: at least one pair of (distinct) provers is consistent. -/
def WeakAccept {ℓ k : ℕ} (code : Fin k → Fin ℓ → Bool) (A : φ.KStrategy ℓ k)
    (r : φ.RandomString ℓ) : Prop :=
  ∃ i i', i ≠ i' ∧ φ.Consistent code A r i i'

/-- Strong acceptance predicate: every pair of provers is consistent. -/
def StrongAccept {ℓ k : ℕ} (code : Fin k → Fin ℓ → Bool) (A : φ.KStrategy ℓ k)
    (r : φ.RandomString ℓ) : Prop :=
  ∀ i i', φ.Consistent code A r i i'

instance {ℓ k : ℕ} (code : Fin k → Fin ℓ → Bool) (A : φ.KStrategy ℓ k) (r : φ.RandomString ℓ) :
    Decidable (φ.WeakAccept code A r) := by
  unfold WeakAccept Consistent; infer_instance

/-- The probability that the verifier of the `k`-prover system weakly accepts: the fraction of
the `(3M)^ℓ` random strings on which the weak acceptance predicate holds. -/
noncomputable def weakAcceptFrac {ℓ k : ℕ} (code : Fin k → Fin ℓ → Bool) (A : φ.KStrategy ℓ k) : ℝ :=
  ((Finset.univ.filter (fun r : φ.RandomString ℓ => φ.WeakAccept code A r)).card : ℝ) /
    Fintype.card (φ.RandomString ℓ)

end Formula5

end SetCoverThreshold.SetCover
