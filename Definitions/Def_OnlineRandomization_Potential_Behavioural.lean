import Mathlib
import Definitions.Def_OnlineRandomization_Potential_Model

namespace OnlineRandomization.Potential

/-- Manuscript p. 14 (Definition 3.1): a randomized online algorithm in behavioural form.
`g (r ++ [x]) a` is the paper's `g_{n+1}(r r_{n+1}, a)`, the law on `A` of the algorithm's next
answer `a_{n+1}` given the requests `r` so far, the new request `r_{n+1} = x`, and the
algorithm's own answers `a` so far. A distribution over deterministic algorithms `G_x` (the
mixed form of p. 7, `RandAlg`) yields it by conditioning on the history; `RandAlg` is kept for
the algorithm `H` of Theorem 3.1, whose coins are shared across request sequences. -/
abbrev BehAlg (R A : Type*) := List R → List A → PMF A

/-- The expectation of a real function under a probability mass function,
`E_p[f] = ∑_z p(z) f(z)`. Every law used here has finite support, so the sum is finite. -/
noncomputable def pexp {X : Type*} (p : PMF X) (f : X → ℝ) : ℝ :=
  ∑' z, (p z).toReal * f z

/-- Manuscript p. 8: the play of a behavioural algorithm `g` against an adaptive on-line
adversary `S`, run for at most `k` more rounds from the configuration `(r, a, b)` (requests,
algorithm's answers, adversary's answers). In each round the adversary's request is
`x = q_n(a)` (stop on `none`), the adversary answers `b_{n+1} = p_n(a)` and the algorithm
answers `a_{n+1} ∼ g(r x, a)`. The result is the law of the final configuration. -/
noncomputable def behPlayAux {R A : Type*} (g : BehAlg R A) (S : OnlineAdv R A) :
    ℕ → List R → List A → List A → PMF (List R × List A × List A)
  | 0, r, a, b => PMF.pure (r, a, b)
  | k + 1, r, a, b =>
    match S.next a with
    | none => PMF.pure (r, a, b)
    | some x => (g (r ++ [x]) a).bind fun a' =>
        behPlayAux g S k (r ++ [x]) (a ++ [a']) (b ++ [S.ans a])

/-- Manuscript p. 8: the law of the final configuration `(r(G,S), a(G,S), b(G,S))` of the
play of `g` against `S` from the empty configuration; `S` stops after at most `d_Q` requests. -/
noncomputable def behPlay {R A : Type*} (g : BehAlg R A) (S : OnlineAdv R A) :
    PMF (List R × List A × List A) :=
  behPlayAux g S S.depth [] [] []

/-- Manuscript p. 9: the behavioural algorithm `g` is `α`-competitive against any adaptive
on-line adversary if `E[c_G(S)] ≤ E[α(c_S(G))]` for every `S`, where `c_G(S) = f_n(r, a)` and
`c_S(G) = f_n(r, b)` at the final configuration; `α` stays inside the expectation, as on p. 9. -/
def IsCompetitiveOnlineBeh {R A : Type*} (F : Game R A) (α : ℝ → ℝ) (g : BehAlg R A) :
    Prop :=
  ∀ S : OnlineAdv R A,
    pexp (behPlay g S) (fun z => F.cost z.1 z.2.1) ≤
      pexp (behPlay g S) (fun z => α (F.cost z.1 z.2.2))

end OnlineRandomization.Potential
