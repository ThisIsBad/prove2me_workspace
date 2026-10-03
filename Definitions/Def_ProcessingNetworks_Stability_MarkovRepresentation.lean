import Mathlib

namespace ProcessingNetworks.Stability

open MeasureTheory ProbabilityTheory Filter

/-- `n`-step transition probabilities of the discrete-time kernel `jump : X → PMF X`. -/
noncomputable def stepIter {X : Type*} (jump : X → PMF X) : ℕ → X → PMF X
  | 0, x => PMF.pure x
  | n + 1, x => (jump x).bind (stepIter jump n)

/-- The chain given by `jump` is irreducible: every state is reachable from every other state in
finitely many steps. -/
def Irreducible {X : Type*} (jump : X → PMF X) : Prop :=
  ∀ x y : X, ∃ n : ℕ, 0 < stepIter jump n x y

/-- `Y` is a discrete-time Markov chain with transition matrix `jump` (Appendix C; the jump chain
`Y` of the sample-path construction in Section D.2): for every `n`, every initial path
`x₀, …, xₙ` and every state `y`,
`P(Y₀ = x₀, …, Yₙ = xₙ, Yₙ₊₁ = y) = P(Y₀ = x₀, …, Yₙ = xₙ) · G(xₙ, y)`. -/
def IsJumpChain {X : Type*} {Ω : Type*} [MeasureSpace Ω] (jump : X → PMF X)
    (Y : ℕ → Ω → X) : Prop :=
  ∀ (n : ℕ) (path : Fin (n + 1) → X) (y : X),
    ℙ {ω | (∀ k : Fin (n + 1), Y k ω = path k) ∧ Y (n + 1) ω = y} =
      ℙ {ω | ∀ k : Fin (n + 1), Y k ω = path k} * jump (path (Fin.last n)) y

/-- The jump times `σ₀ = 0`, `σₙ₊₁ = σₙ + τₙ / λ(Yₙ)` of the sample-path construction (D.6): the
chain holds in the state `Yₙ` for the time `τₙ / λ(Yₙ)`, where `τₙ` is a unit-mean exponential
clock and `λ(Yₙ)` the exit rate of that state. -/
noncomputable def jumpTime {X : Type*} {Ω : Type*} (rate : X → ℝ) (Y : ℕ → Ω → X)
    (clock : ℕ → Ω → ℝ) : ℕ → Ω → ℝ
  | 0, _ => 0
  | n + 1, ω => jumpTime rate Y clock n ω + clock n ω / rate (Y n ω)

/-- Assumption 3.1 (Markov representation), Dai & Harrison, p. 46: there is an irreducible
continuous-time Markov chain `X = {X(t), t ≥ 0}` on a countable state space `Xstate`, together
with a function `f : Xstate → (Fin J → ℕ) × (Fin I → ℕ)` such that `(N(t), Z(t)) = f(X(t))` on
every sample path (Eq. 3.1); the set `B(z) := {x | ∃ n, f x = (n, z)}` is finite for every `z`
(Eq. 3.2); and there is an empty state `x0` with `f x0 = (0, 0)` (Eq. 3.3).

Following Appendix D (Definition D.6 and the sentence after it: "Whenever a CTMC `X` is mentioned,
without loss of generality we envision `X` to be constructed as in (D.5)"), the chain is recorded
through its regular generator and the sample-path construction (D.5)–(D.6): `jump` is the jump
matrix `G` (with `G(x, x) = 0`, Eq. (D.2)), `rate x = λ(x) > 0` the exit rate of `x`, `Y` the
embedded jump chain (a discrete-time Markov chain with transition matrix `G`), `clock n = τₙ` i.i.d.
unit-mean exponential clocks independent of `Y`, `jumpTime rate Y clock n = σₙ` the jump times,
`X(t) = Yₙ` on `[σₙ, σₙ₊₁)`, and `σₙ → ∞` on every sample path (the generator is non-explosive,
Definition D.2/D.3). Irreducibility of `X` is irreducibility of its jump chain (Definition D.10). -/
structure MarkovRepresentation (Xstate : Type*) [Countable Xstate] {Ω : Type*} [MeasureSpace Ω]
    (I J : ℕ) (N : ℝ → Ω → Fin J → ℕ) (Z : ℝ → Ω → Fin I → ℕ) where
  jump : Xstate → PMF Xstate
  rate : Xstate → ℝ
  Y : ℕ → Ω → Xstate
  clock : ℕ → Ω → ℝ
  X : ℝ → Ω → Xstate
  f : Xstate → (Fin J → ℕ) × (Fin I → ℕ)
  rate_pos : ∀ x, 0 < rate x
  jump_irrefl : ∀ x, jump x x = 0
  jump_chain : IsJumpChain jump Y
  clock_pos : ∀ (n : ℕ) (ω : Ω), 0 < clock n ω
  clock_exp : ∀ (n : ℕ) (s : ℝ), 0 ≤ s → ℙ {ω | s < clock n ω} = ENNReal.ofReal (Real.exp (-s))
  clock_iid : iIndepFun clock ℙ
  clock_indep_jumpChain :
    Indep (MeasurableSpace.comap (fun ω => fun n => clock n ω) inferInstance)
      (MeasurableSpace.comap (fun ω => fun n => Y n ω) ⊤) ℙ
  nonexplosive : ∀ ω : Ω, Tendsto (fun n => jumpTime rate Y clock n ω) atTop atTop
  sample_path : ∀ (ω : Ω) (n : ℕ) (t : ℝ),
    jumpTime rate Y clock n ω ≤ t → t < jumpTime rate Y clock (n + 1) ω → X t ω = Y n ω
  irreducible : Irreducible jump
  sample_path_eq : ∀ (t : ℝ) (ω : Ω), (N t ω, Z t ω) = f (X t ω)
  finite_fiber : ∀ z : Fin I → ℕ, {x : Xstate | ∃ n : Fin J → ℕ, f x = (n, z)}.Finite
  empty_state : ∃ x0 : Xstate, f x0 = (0, 0)

/-- The size `|x| := |z| := ∑ᵢ zᵢ` of a state `x` with `f x = (n, z)`, Eq. (3.4). -/
noncomputable def MarkovRepresentation.size {Xstate : Type*} [Countable Xstate] {Ω : Type*}
    [MeasureSpace Ω] {I J : ℕ} {N : ℝ → Ω → Fin J → ℕ} {Z : ℝ → Ω → Fin I → ℕ}
    (M : MarkovRepresentation Xstate I J N Z) (x : Xstate) : ℝ :=
  ∑ i, ((M.f x).2 i : ℝ)

/-- The number of jumps of the ambient chain in `(0, t]`: `#{n ≥ 1 : σₙ ≤ t}` (finite on every
sample path, by non-explosion). -/
noncomputable def MarkovRepresentation.jumpCount {Xstate : Type*} [Countable Xstate] {Ω : Type*}
    [MeasureSpace Ω] {I J : ℕ} {N : ℝ → Ω → Fin J → ℕ} {Z : ℝ → Ω → Fin I → ℕ}
    (M : MarkovRepresentation Xstate I J N Z) (t : ℝ) (ω : Ω) : ℕ :=
  {n : ℕ | 1 ≤ n ∧ jumpTime M.rate M.Y M.clock n ω ≤ t}.ncard

/-- A cumulative-count process `V` is embedded in the ambient chain as a functional of its jumps:
`V(t)` is the sum, over the jumps of `X` in `(0, t]`, of an increment `g(x, y)` determined by
the state `x` left and the state `y` entered (so `V` jumps only when `X` does, by an amount read
off the transition — e.g. the routing increments `ΔV(t) = g(Z(t-), δ)` of (4.8) at the
arrival transitions of the ambient chain). -/
def IsJumpFunctional {Xstate : Type*} [Countable Xstate] {Ω : Type*} [MeasureSpace Ω]
    {I J : ℕ} {N : ℝ → Ω → Fin J → ℕ} {Z : ℝ → Ω → Fin I → ℕ}
    (M : MarkovRepresentation Xstate I J N Z) {α : Type*} [AddCommMonoid α]
    (V : ℝ → Ω → α) (g : Xstate → Xstate → α) : Prop :=
  ∀ (t : ℝ) (ω : Ω), 0 ≤ t →
    V t ω = ∑ n ∈ Finset.range (M.jumpCount t ω), g (M.Y n ω) (M.Y (n + 1) ω)

end ProcessingNetworks.Stability
