import Mathlib

namespace HeldWolfeCrowder.Assignment

/-- Held–Wolfe–Crowder (1974), §3, p. 69. The cost `c = Σ_r a_{A(r) r}` of an *assignment*
`A : Fin n → Fin n`, where `A r` is the man assigned to job `r` and `a i r` is the cost for which
man `i` does job `r`. Two jobs may be assigned to the same man. -/
def assignCost {n : ℕ} (a : Matrix (Fin n) (Fin n) ℝ) (A : Fin n → Fin n) : ℝ :=
  ∑ r, a (A r) r

/-- The vector `v` of Eq. (3.4), p. 69: `(v_A)_i = 1 − #{r : A(r) = i}`. -/
def assignVec {n : ℕ} (A : Fin n → Fin n) (i : Fin n) : ℝ :=
  1 - ((Finset.univ.filter fun r => A r = i).card : ℝ)

/-- A one-to-one assignment `σ` (a permutation; `σ r` is the man doing job `r`) is *optimal* for
the assignment problem (3.1), p. 69, if its total cost is minimal among all one-to-one
assignments. -/
def IsOptimalAssignment {n : ℕ} (a : Matrix (Fin n) (Fin n) ℝ) (σ : Equiv.Perm (Fin n)) : Prop :=
  ∀ τ : Equiv.Perm (Fin n), assignCost a σ ≤ assignCost a τ

/-- The dual function (3.3), p. 69: `w(π) = Σ_i π_i + Σ_r min_s [a_{sr} − π_s]`, the minimum
for job `r` being over the man index `s`. (The index set of the minimum is nonempty because it
contains `r`, so the definition is valid for every `n`.) -/
def w {n : ℕ} (a : Matrix (Fin n) (Fin n) ℝ) (π : Fin n → ℝ) : ℝ :=
  ∑ i, π i + ∑ r, Finset.univ.inf' ⟨r, Finset.mem_univ r⟩ (fun s => a s r - π s)

/-- The optimal set of the problem `max w` for (3.3): all `π` at which `w` attains its
maximum. -/
def optSet {n : ℕ} (a : Matrix (Fin n) (Fin n) ℝ) : Set (Fin n → ℝ) :=
  {π | ∀ π' : Fin n → ℝ, w a π' ≤ w a π}

/-- The set `Π` of Eq. (3.6), p. 70, for a one-to-one assignment `σ`: all `π` with
`a_{ir} − π_i > a_{σ(r) r} − π_{σ(r)}` for every job `r` and every man `i ≠ σ(r)`. -/
def PiSet {n : ℕ} (a : Matrix (Fin n) (Fin n) ℝ) (σ : Equiv.Perm (Fin n)) : Set (Fin n → ℝ) :=
  {π | ∀ r i : Fin n, i ≠ σ r → a (σ r) r - π (σ r) < a i r - π i}

end HeldWolfeCrowder.Assignment
