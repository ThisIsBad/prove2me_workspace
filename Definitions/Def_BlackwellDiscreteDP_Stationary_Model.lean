import Mathlib
import Definitions.Def_FoundationsML_ReinforcementLearning_IsTransitionKernel

namespace BlackwellDiscreteDP.Stationary

/-- Blackwell's finite decision model (Blackwell, *Discrete Dynamic Programming*,
Ann. Math. Statist. 33(2):719–726 (1962), DOI 10.1214/aoms/1177704593, §1–§2, p. 719).

States form the finite type `St` (Blackwell's `1, …, S`) and actions the finite type `Act`
(Blackwell's finite set `A`); every action is available in every state. `income s a` is the
immediate income `i(s, a)` (a real number of either sign) and `law s a s'` is the transition
probability `q(s' | s, a)`, which for each `(s, a)` is a probability vector in `s'`.

**Formalization Note.** The stochasticity of the law of motion is the published predicate
`FoundationsML.ReinforcementLearning.IsTransitionKernel` (`0 ≤ q(s'|s,a)` and
`∑_{s'} q(s'|s,a) = 1`), with the same argument order `law s a s' = q(s' | s, a)`. -/
structure Model (St Act : Type) [Fintype St] where
  /-- The immediate income `i(s, a)`. -/
  income : St → Act → ℝ
  /-- The law of motion: `law s a s' = q(s' | s, a)`. -/
  law : St → Act → St → ℝ
  /-- For every `(s, a)`, `q(· | s, a)` is a probability vector. -/
  law_kernel : FoundationsML.ReinforcementLearning.IsTransitionKernel law

/-- A policy `π = {f_n, n = 1, 2, ⋯}` (p. 719): a sequence of decision rules `f_n ∈ F`, where
`F` is the set of functions from states to actions.

**Formalization Note.** The sequence is indexed from `0`: `π 0` is Blackwell's `f₁` and
`π n` is `f_{n+1}`. -/
abbrev Policy (St Act : Type) : Type := ℕ → St → Act

/-- The policy `(f, π)` (p. 719, the case `N = 1` of `(g₁, ⋯, g_N, π)`): use `f` on the first
day, then follow `π` from the second day on (`h₁ = f`, `h_n = f_{n−1}` for `n > 1`). -/
def Policy.cons {St Act : Type} (f : St → Act) (π : Policy St Act) : Policy St Act :=
  fun n => Nat.casesOn n f (fun m => π m)

/-- The policy `(g₁, ⋯, g_N, π)` (p. 719): `h_n = g_n` for `1 ≤ n ≤ N`, `h_n = f_{n−N}` for
`n > N`. The list `[g₁, …, g_N]` is prepended to `π`. -/
def Policy.prepend {St Act : Type} (gs : List (St → Act)) (π : Policy St Act) :
    Policy St Act :=
  gs.foldr Policy.cons π

/-- The policy `g^(N), π` (p. 719): `h_n = g` for `1 ≤ n ≤ N`, `h_n = f_{n−N}` for `n > N`. -/
def Policy.repeatThen {St Act : Type} (g : St → Act) (N : ℕ) (π : Policy St Act) :
    Policy St Act :=
  fun n => if n < N then g else π (n - N)

/-- The stationary policy `g^(∞)` (p. 719): `h_n = g` for all `n`. -/
def stationary {St Act : Type} (g : St → Act) : Policy St Act :=
  fun _ => g

/-- The shifted policy `Tπ` (p. 719): `h_n = f_{n+1}`. -/
def Policy.shift {St Act : Type} (π : Policy St Act) : Policy St Act :=
  fun n => π (n + 1)

namespace Model

variable {St Act : Type} [Fintype St]

/-- `r(f)` (p. 719): the `S × 1` income vector whose `s`th element is `i(s, f(s))`. -/
def r (M : Model St Act) (f : St → Act) : St → ℝ :=
  fun s => M.income s (f s)

/-- `Q(f)` (p. 719): the `S × S` Markov matrix whose `(s, s')` element is `q(s' | s, f(s))`. -/
def Q (M : Model St Act) (f : St → Act) : Matrix St St ℝ :=
  Matrix.of fun s s' => M.law s (f s) s'

/-- `Q_n(π) = Q(f₁) Q(f₂) ⋯ Q(f_n)` (p. 719), with `Q₀(π) = I` (p. 720). The product is the
ordered matrix product: `Q_{n+1}(π) = Q_n(π) Q(f_{n+1})`, and `f_{n+1}` is `π n`. -/
def Qn [DecidableEq St] (M : Model St Act) (π : Policy St Act) : ℕ → Matrix St St ℝ
  | 0 => 1
  | n + 1 => Qn M π n * M.Q (π n)

/-- The total expected discounted return of `π` (p. 719),
`V_β(π) = ∑_{n=0}^∞ βⁿ Q_n(π) r(f_{n+1})`, a vector indexed by the initial state.

**Formalization Note.** The sum is the `tsum` in `St → ℝ`. Blackwell takes `0 ≤ β < 1`, and every
statement using `V` assumes this; then the entries of `Q_n(π)` lie in `[0, 1]`, `r` is bounded,
and the series converges absolutely, so the `tsum` is the genuine sum (it would be `0` only for a
non-summable series, which does not occur for `0 ≤ β < 1`). -/
noncomputable def V [DecidableEq St] (M : Model St Act) (β : ℝ) (π : Policy St Act) : St → ℝ :=
  ∑' n : ℕ, β ^ n • (M.Qn π n).mulVec (M.r (π n))

/-- The transformation `L(f)` (p. 720): `L(f)w = r(f) + βQ(f)w` for an `S × 1` vector `w`. -/
def L (M : Model St Act) (β : ℝ) (f : St → Act) (w : St → ℝ) : St → ℝ :=
  M.r f + β • (M.Q f).mulVec w

/-- `π*` is optimal in the sense of §3 (p. 720), here called **β-optimal** as in §4 (p. 721):
`π* ≧ π` for all policies `π`, i.e. `V_β(π*) ≧ V_β(π)` coordinatewise for every policy `π`
(deterministic Markov, possibly time-dependent). -/
def IsBetaOptimal [DecidableEq St] (M : Model St Act) (β : ℝ) (πstar : Policy St Act) : Prop :=
  ∀ π : Policy St Act, M.V β π ≤ M.V β πstar

/-- The set `G(s, f)` of Theorem 3 (p. 720): all actions `a` with
`i(s, a) + β p(s, a) V(f^(∞)) > V_s(f^(∞))`, where `p(s, a)` is the row vector
`(q(s' | s, a))_{s'}` and `V_s(f^(∞))` is the `s`th coordinate of `V_β(f^(∞))`. -/
def G [DecidableEq St] (M : Model St Act) (β : ℝ) (f : St → Act) (s : St) : Set Act :=
  {a | M.V β (stationary f) s <
      M.income s a + β * ∑ s' : St, M.law s a s' * M.V β (stationary f) s'}

/-- A policy is **optimal** in the sense of §4 (p. 721): it is β-optimal for all `β`
sufficiently near `1`, i.e. there is `β₀ < 1` such that it is β-optimal for every
`β ∈ (β₀, 1)`. (Today this is called Blackwell optimality.)

**Formalization Note.** This is a different notion from the §3 "optimal", which is
`IsBetaOptimal β` at one fixed `β`. Blackwell phrases it as `V_β(π) = U(β)` for all `β`
sufficiently near `1`, where `U(β)` is the return of a β-optimal policy; since `U(β) ≧ V_β(π')`
for every `π'`, that is the same as `IsBetaOptimal β π`, and no supremum over policies is
needed. -/
def IsOptimal [DecidableEq St] (M : Model St Act) (π : Policy St Act) : Prop :=
  ∃ β₀ : ℝ, β₀ < 1 ∧ ∀ β : ℝ, β₀ < β → β < 1 → M.IsBetaOptimal β π

end Model

end BlackwellDiscreteDP.Stationary
