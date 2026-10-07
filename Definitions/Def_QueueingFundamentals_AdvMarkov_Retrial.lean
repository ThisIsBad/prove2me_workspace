import Mathlib

namespace QueueingFundamentals.AdvMarkov

/-- The rate-balance equations (3.47)–(3.49), p.159, of the `M/M/1` retrial queue (§3.5.1) with
arrival rate `λ`, service rate `μ` and retrial rate `γ` per customer in orbit. The state `{i, n}`
has `i ∈ {0, 1}` customers in service and `n` in orbit; `p0 n = p_{0,n}` and `p1 n = p_{1,n}`.
* (3.47) `(λ + nγ) p_{0,n} = μ p_{1,n}` for `n ≥ 0`;
* (3.48) `(λ + μ) p_{1,n} = λ p_{0,n} + (n + 1)γ p_{0,n+1} + λ p_{1,n−1}` for `n ≥ 1`;
* (3.49) `(λ + μ) p_{1,0} = λ p_{0,0} + γ p_{0,1}`. -/
def RetrialBalance (lam mu gam : ℝ) (p0 p1 : ℕ → ℝ) : Prop :=
  (∀ n : ℕ, (lam + (n : ℝ) * gam) * p0 n = mu * p1 n) ∧
    (∀ n : ℕ, 1 ≤ n →
      (lam + mu) * p1 n = lam * p0 n + ((n : ℝ) + 1) * gam * p0 (n + 1) + lam * p1 (n - 1)) ∧
    (lam + mu) * p1 0 = lam * p0 0 + gam * p0 1

/-- A steady-state solution of the `M/M/1` retrial queue (book convention, §1.9 p.34 and the
footnote on p.118): a probability distribution `{p_{i,n}}` on `{0, 1} × {0, 1, 2, …}` —
nonnegative, with total mass `∑_n (p_{0,n} + p_{1,n}) = 1` — that solves (3.47)–(3.49). -/
def IsRetrialSteadyState (lam mu gam : ℝ) (p0 p1 : ℕ → ℝ) : Prop :=
  (∀ n : ℕ, 0 ≤ p0 n) ∧ (∀ n : ℕ, 0 ≤ p1 n) ∧ HasSum (fun n : ℕ => p0 n + p1 n) 1 ∧
    RetrialBalance lam mu gam p0 p1

/-- The (partial) generating function `∑_{n ≥ 0} zⁿ p_n` of a sequence, for a real argument `z`
(p.159: `P_0(z) ≡ ∑ zⁿ p_{0,n}`, `P_1(z) ≡ ∑ zⁿ p_{1,n}`). -/
noncomputable def pgf (p : ℕ → ℝ) (z : ℝ) : ℝ :=
  ∑' n : ℕ, z ^ n * p n

/-- The closed form of `p_{0,n}` in (3.57), p.161, with `ρ = λ/μ`:
`p_{0,n} = (1 − ρ)^{(λ/γ)+1} · ρⁿ/(n! γⁿ) · ∏_{i=0}^{n−1} (λ + iγ)` (empty product `= 1`).
The exponent `(λ/γ) + 1` is a real power (`Real.rpow`). -/
noncomputable def retrialP0 (lam mu gam : ℝ) (n : ℕ) : ℝ :=
  (1 - lam / mu) ^ (lam / gam + 1) * ((lam / mu) ^ n / ((n.factorial : ℝ) * gam ^ n)) *
    ∏ i ∈ Finset.range n, (lam + (i : ℝ) * gam)

/-- The closed form of `p_{1,n}` in (3.57), p.161, with `ρ = λ/μ`:
`p_{1,n} = (1 − ρ)^{(λ/γ)+1} · ρ^{n+1}/(n! γⁿ) · ∏_{i=1}^{n} (λ + iγ)` (empty product `= 1`). -/
noncomputable def retrialP1 (lam mu gam : ℝ) (n : ℕ) : ℝ :=
  (1 - lam / mu) ^ (lam / gam + 1) * ((lam / mu) ^ (n + 1) / ((n.factorial : ℝ) * gam ^ n)) *
    ∏ i ∈ Finset.Icc 1 n, (lam + (i : ℝ) * gam)

end QueueingFundamentals.AdvMarkov
