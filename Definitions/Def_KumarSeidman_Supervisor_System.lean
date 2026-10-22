import Mathlib

namespace KumarSeidman.Supervisor

/-- A manufacturing system in the sense of Kumar–Seidman (1990), §I, items 1–4 (p. 289).
There are `P` part types (`Fin P`) and `M` machines (`Fin M`). Part type `p` visits the
`n p ≥ 1` machines `μ p 0, μ p 1, …, μ p (n p - 1)` in this order (the paper's
`μ_{p,1}, …, μ_{p,n_p}`; Lean index `i` is the paper's index `i + 1`); revisits are allowed.
It enters the system at rate `d p > 0`, its `i`-th operation takes `τ p i > 0` time units per
part, and switching a machine from buffer `b` to buffer `b'` costs a set-up time
`δ b b' ≥ 0`; continuing on the same buffer costs nothing (`δ b b = 0`). -/
structure System (P M : ℕ) where
  n : Fin P → ℕ
  n_pos : ∀ p, 0 < n p
  μ : (p : Fin P) → Fin (n p) → Fin M
  d : Fin P → ℝ
  d_pos : ∀ p, 0 < d p
  τ : (p : Fin P) → Fin (n p) → ℝ
  τ_pos : ∀ p i, 0 < τ p i
  δ : (Σ p : Fin P, Fin (n p)) → (Σ p : Fin P, Fin (n p)) → ℝ
  δ_nonneg : ∀ b b', 0 ≤ δ b b'
  δ_self : ∀ b, δ b b = 0

variable {P M : ℕ}

/-- The buffers `b_{p,i}`: one per (part type, stage of its route). -/
abbrev Buffer (S : System P M) := Σ p : Fin P, Fin (S.n p)

/-- The machine `μ_{p,i}` serving buffer `b = b_{p,i}`. -/
def System.mach (S : System P M) (b : Buffer S) : Fin M := S.μ b.1 b.2

/-- The processing time `τ_{p,i}` of buffer `b = b_{p,i}`. -/
def System.tau (S : System P M) (b : Buffer S) : ℝ := S.τ b.1 b.2

/-- `B_m = {b_{p,i} : μ_{p,i} = m}`, the buffers served by machine `m`. -/
def System.B (S : System P M) (m : Fin M) : Finset (Buffer S) :=
  Finset.univ.filter (fun b => S.mach b = m)

/-- The buffer preceding `b_{p,i}` on the route of part type `p`, i.e. `b_{p,i-1}`;
`none` for the first buffer of a route (parts arrive there from outside). -/
def System.prev (S : System P M) (b : Buffer S) : Option (Buffer S) :=
  if h : 0 < b.2.val then some ⟨b.1, ⟨b.2.val - 1, by omega⟩⟩ else none

/-- `ρ_m = Σ_{(p,i) : μ_{p,i} = m} d_p τ_{p,i}`, the load of machine `m` in (1) (p. 290). -/
noncomputable def System.rho (S : System P M) (m : Fin M) : ℝ :=
  ∑ b ∈ S.B m, S.d b.1 * S.tau b

/-- The capacity condition (1) (p. 290): `ρ_m < 1` for every machine `m`. -/
def System.CapacityCondition (S : System P M) : Prop := ∀ m, S.rho m < 1

/-- `Σ_{b ∈ B_m} max_{b' ∈ B_m} δ_{b',b}`, the set-up allowance of (24) and (26) (p. 296).
The maximum is over the nonempty set `B_m ∋ b` (`Finset.sup'`); the sum is `0` when `B_m` is
empty. -/
noncomputable def System.setupSum (S : System P M) (m : Fin M) : ℝ :=
  ∑ b ∈ (S.B m).attach, (S.B m).sup' ⟨b.1, b.2⟩ (fun b' => S.δ b' b.1)

end KumarSeidman.Supervisor
