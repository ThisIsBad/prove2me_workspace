import Mathlib

namespace NSWApxHard.Reduction

open Finset

section Generic

variable {A B : Type} [Fintype A] [Fintype B] [DecidableEq A]

/-- Additive utility of agent `a` under the allocation `x` (Lee, p. 1): `x` sends every item to
exactly one agent (the partition `{B_a}`), and `u_a(x) = ∑_{i ∈ B_a} u a i`. -/
def utility (u : A → B → ℝ) (x : B → A) (a : A) : ℝ :=
  ∑ i ∈ univ.filter (fun i => x i = a), u a i

/-- Nash social welfare of the allocation `x` (Lee, p. 1): the geometric mean
`(∏_a u_a(x))^{1/n}` of the agents' utilities, `n = |A|`. -/
noncomputable def nsw (u : A → B → ℝ) (x : B → A) : ℝ :=
  (∏ a, utility u x a) ^ ((1 : ℝ) / Fintype.card A)

/-- `x` maximizes the Nash social welfare over all allocations. -/
def IsOptimal (u : A → B → ℝ) (x : B → A) : Prop :=
  ∀ y : B → A, nsw u y ≤ nsw u x

end Generic

/-- Self-delimiting binary code of a natural number: each binary digit of `k` (least significant
first, as in `Nat.bits`) is preceded by `true`, and the code ends with `false`. Its length is
`2 ⌈log₂ (k + 1)⌉ + 1`. -/
def natBits (k : ℕ) : List Bool :=
  (Nat.bits k).flatMap (fun b => [true, b]) ++ [false]

/-- An input of the Nash-social-welfare decision problem: `n` agents, `m` items, natural-number
utilities `u a i`, and a natural-number threshold `T` for the product of the utilities. -/
structure NSWInput where
  n : ℕ
  m : ℕ
  u : Fin n → Fin m → ℕ
  T : ℕ

namespace NSWInput

/-- The binary encoding of an input: `n`, `m`, `T`, then the utilities `u a i` row by row (agent
`a = 0, …, n-1`, and within a row item `i = 0, …, m-1`), every number by `natBits`. -/
def enc (P : NSWInput) : List Bool :=
  natBits P.n ++ natBits P.m ++ natBits P.T ++
    (List.ofFn fun a : Fin P.n => (List.ofFn fun i : Fin P.m => natBits (P.u a i)).flatten).flatten

/-- Nash social welfare of the allocation `x` (item `i` goes to agent `x i`) in the input `P`. -/
noncomputable def nswOf (P : NSWInput) (x : Fin P.m → Fin P.n) : ℝ :=
  nsw (fun a i => (P.u a i : ℝ)) x

/-- The welfare threshold `τ = T^{1/n}` of the input: `nswOf x ≥ τ` iff the product of the
utilities is at least `T`. -/
noncomputable def tau (P : NSWInput) : ℝ :=
  (P.T : ℝ) ^ ((1 : ℝ) / P.n)

end NSWInput

/-- The encoding of NSW inputs used for the complexity statements. -/
def encNSW (P : NSWInput) : List Bool := P.enc

/-- Yes-instances of the gap problem: at least one agent, `n ≤ m` (Lee, p. 1), `T ≥ 1`, and some
allocation has Nash social welfare at least `τ`. -/
def nswYes (P : NSWInput) : Prop :=
  1 ≤ P.n ∧ P.n ≤ P.m ∧ 1 ≤ P.T ∧ ∃ x : Fin P.m → Fin P.n, P.tau ≤ P.nswOf x

/-- No-instances of the gap problem for the factor `μ`: at least one agent, `n ≤ m`, `T ≥ 1`, and
every allocation has Nash social welfare at most `τ / μ`. -/
def nswNo (μ : ℝ) (P : NSWInput) : Prop :=
  1 ≤ P.n ∧ P.n ≤ P.m ∧ 1 ≤ P.T ∧ ∀ x : Fin P.m → Fin P.n, P.nswOf x ≤ P.tau / μ

end NSWApxHard.Reduction
