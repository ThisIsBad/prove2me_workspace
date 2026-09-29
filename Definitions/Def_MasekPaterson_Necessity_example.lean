import Mathlib
import Definitions.Def_MasekPaterson_Shared_editDist
import Definitions.Def_MasekPaterson_Necessity_editPaths
open MasekPaterson.Shared

namespace MasekPaterson.Necessity

/-- The alphabet `Σ = {a, b, c}` of the example of §4.1. -/
inductive Sym
  | a
  | b
  | c
  deriving DecidableEq, Repr

/-- The alphabet `Σ = {a, b, c}` is finite. -/
instance : Fintype Sym :=
  ⟨{Sym.a, Sym.b, Sym.c}, fun x => by cases x <;> simp⟩

/-- The replacement costs of the example: `R_{σ,σ} = 0`, `R_{a,b} = R_{b,a} = 1`,
`R_{c,b} = R_{c,a} = R_{a,c} = R_{b,c} = π`. -/
noncomputable def exRepl : Sym → Sym → ℝ
  | .a, .a => 0
  | .b, .b => 0
  | .c, .c => 0
  | .a, .b => 1
  | .b, .a => 1
  | .c, .b => Real.pi
  | .c, .a => Real.pi
  | .a, .c => Real.pi
  | .b, .c => Real.pi

/-- The cost function `γ` of the example: a replacement `x → y` costs `R_{x,y}` (`exRepl`),
and every insertion and every deletion costs `I_σ = D_σ = 5`. (The pair `(λ, λ)` is not an
edit operation; the last branch covers exactly the deletions and insertions.) -/
noncomputable def exCost (o : EditOp Sym) : ℝ :=
  match o.src, o.tgt with
  | some x, some y => exRepl x y
  | _, _ => 5

/-- `μ_i = ⌊2⌊i/2⌋ / (2π + 1)⌋`, i.e. `μ_{2k} = μ_{2k+1} = ⌊2k / (2π + 1)⌋`. -/
noncomputable def mu (i : ℕ) : ℕ :=
  ⌊((2 * (i / 2) : ℕ) : ℝ) / (2 * Real.pi + 1)⌋₊

/-- The infinite string `A` of the example, 1-based (`exA i` is `A_i` for `i ≥ 1`; the
value at `0` is never used): `A' = baba…` with `c` put in the even positions `i` where
`μ_i > μ_{i-1}`, so that `A^i` contains exactly `μ_i` letters `c`. -/
noncomputable def exA (i : ℕ) : Sym :=
  if i % 2 = 1 then .b else if mu (i - 1) < mu i then .c else .a

/-- The infinite string `B` of the example, 1-based: `B' = abab…` with `c` put in the same
even positions as in `A`. -/
noncomputable def exB (i : ℕ) : Sym :=
  if i % 2 = 1 then .a else if mu (i - 1) < mu i then .c else .b

/-- The prefix `A^n = A_1 ⋯ A_n` of length `n`. -/
noncomputable def exAPre (n : ℕ) : List Sym := List.ofFn fun t : Fin n => exA (t.val + 1)

/-- The prefix `B^n = B_1 ⋯ B_n` of length `n`. -/
noncomputable def exBPre (n : ℕ) : List Sym := List.ofFn fun t : Fin n => exB (t.val + 1)

/-- The edit matrix entry `δ_{i,j} = δ(γ, A^i, B^j)` of the example. -/
noncomputable def exDelta (i j : ℕ) : ℝ := editDist exCost (exAPre i) (exBPre j)

/-- `P(i, j, k)`: the minimum cost of an edit path from `(i, j)` to `(i + k, j + k)`. -/
noncomputable def exP (i j k : ℕ) : ℝ := pathMin exCost exA exB (i, j) (i + k, j + k)

/-- `P*(i, j, k)`: the minimum cost of an edit path from `(i, j)` to `(i + k, j + k)` all of
whose points (endpoints included) have eccentricity at least `|i - j|`. -/
noncomputable def exPstar (i j k : ℕ) : ℝ :=
  sInf {c : ℝ | ∃ ms : List Move, pathEnd (i, j) ms = (i + k, j + k) ∧
    (∀ x ∈ pathPoints (i, j) ms, ecc (i, j) ≤ ecc x) ∧
    c = pathCost exCost exA exB (i, j) ms}

end MasekPaterson.Necessity
