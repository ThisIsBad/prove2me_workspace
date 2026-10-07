import Mathlib

namespace SchedComplexity.PrecChain

/-- An instance of the problem class `n|m|I,prec,1≤p_j1≤p_*|k` of Brucker, Lenstra &
Rinnooy Kan (Report BW 43/75, 1975, Section 3, pp. 6–7), before the class restrictions are
imposed: `n` single-operation jobs `J_j` (`Fin n`, 0-based: the paper's `J_{j+1}` is `j`),
`m` identical parallel machines (`ℓ = I`), the processing time `p j` of each job, and the
precedence relation given as a Boolean matrix: `prec j k = true` means `J_j < J_k`
("`J_j` precedes `J_k`"). Weights, release dates and due dates do not occur: the criteria of
this mission are `C_max` and `Σ_j C_j` (`w_j = 1`), and all jobs are available at time `0`. -/
structure Instance where
  /-- the number of jobs -/
  n : ℕ
  /-- the number of identical machines -/
  m : ℕ
  /-- the processing times `p_j` -/
  p : Fin n → ℕ
  /-- the precedence relation: `prec j k = true` iff `J_j < J_k` -/
  prec : Fin n → Fin n → Bool

namespace Instance

variable (I : Instance)

/-- `J_j < J_k`: job `j` is required to precede job `k`. -/
def Precedes (j k : Fin I.n) : Prop := I.prec j k = true

/-- The precedence relation is acyclic: no job precedes itself through a chain
`J_j < … < J_j` of length at least one. -/
def Acyclic : Prop := ∀ j : Fin I.n, ¬ Relation.TransGen I.Precedes j j

/-- Membership in the class `n|m|I,prec,1≤p_j1≤p_*` for the constant `p_*` (p. 7): at least one
machine, every processing time in `[1, p_*]` (the element `1≤p_jr≤p_*` of `λ`), and acyclic
precedence constraints (the paper's `prec` is a precedence order between the jobs; a cyclic
relation admits no schedule at all). -/
def InClass (pstar : ℕ) : Prop :=
  1 ≤ I.m ∧ (∀ j : Fin I.n, 1 ≤ I.p j ∧ I.p j ≤ pstar) ∧ I.Acyclic

end Instance

/-- A nonpreemptive schedule of an instance `I` on its identical machines: job `j` is processed
on machine `machine j` (`Fin I.m`, 0-based: machine `0` is the paper's `M_1`) from its starting
time `start j = B_j`, a natural number. Start times are natural numbers because Section 3
(p. 6) computes the times `B_j`, `C_j` from processing orders on integer data. -/
structure Schedule (I : Instance) where
  /-- the machine processing each job -/
  machine : Fin I.n → Fin I.m
  /-- the starting time `B_j` of each job -/
  start : Fin I.n → ℕ

namespace Schedule

variable {I : Instance} (σ : Schedule I)

/-- The completion time `C_j = B_j + p_j`. -/
def completion (j : Fin I.n) : ℕ := σ.start j + I.p j

/-- Feasibility (p. 6 and p. 7): two distinct jobs on the same machine are processed one after
the other ("each machine can handle at most one job at a time"), and `J_j < J_k` implies
`C_j ≤ B_k` (the element `prec` of `λ`). Idle time is allowed. -/
def IsFeasible : Prop :=
  (∀ j k : Fin I.n, j ≠ k → σ.machine j = σ.machine k →
      σ.completion j ≤ σ.start k ∨ σ.completion k ≤ σ.start j) ∧
    (∀ j k : Fin I.n, I.Precedes j k → σ.completion j ≤ σ.start k)

/-- The total completion time `Σ_j C_j`, i.e. `Σ_j w_j C_j` with `w_j = 1` (p. 7). -/
def totalCompletion : ℕ := ∑ j : Fin I.n, σ.completion j

end Schedule

/-- The yes-instances of the recognition version of `C_max` (Section 2, p. 4): some feasible
schedule has `C_max ≤ y`, written as `C_j ≤ y` for every job `j` (which is `max_j C_j ≤ y` when
`n ≥ 1`, and holds for `n = 0`). -/
def CmaxYes (I : Instance) (y : ℕ) : Prop :=
  ∃ σ : Schedule I, σ.IsFeasible ∧ ∀ j : Fin I.n, σ.completion j ≤ y

/-- The yes-instances of the recognition version of `Σ_j C_j`: some feasible schedule has
`Σ_j C_j ≤ y`. -/
def SumCYes (I : Instance) (y : ℕ) : Prop :=
  ∃ σ : Schedule I, σ.IsFeasible ∧ σ.totalCompletion ≤ y

end SchedComplexity.PrecChain
