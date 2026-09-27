import Mathlib

namespace KellyStochasticNetworks

/-- `ackAttemptRate h t = h(1) + ⋯ + h(t)`.  In an acknowledgement-based scheme, `h x` is the
probability that a packet attempts transmission `x` slots after its arrival (`h 1 = 1`), and on
an externally jammed channel the number of attempts in slot `t` is Poisson with mean
`ν · ackAttemptRate h t`.  Kelly–Yudovina, *Stochastic Networks*, p. 120. -/
def ackAttemptRate (h : ℕ → ℝ) (t : ℕ) : ℝ := ∑ r ∈ Finset.Icc 1 t, h r

/-- `P_t`, the probability that fewer than two transmission attempts are made in slot `t` of the
externally jammed channel: `(1 + ν ∑_{r ≤ t} h(r)) exp(-ν ∑_{r ≤ t} h(r))`. -/
noncomputable def ackSlotProb (h : ℕ → ℝ) (ν : ℝ) (t : ℕ) : ℝ :=
  (1 + ν * ackAttemptRate h t) * Real.exp (-(ν * ackAttemptRate h t))

/-- The ALOHA retransmission function of Example 5.8: `h 1 = 1`, and `h x = f` for `x > 1`. -/
def alohaH (f : ℝ) : ℕ → ℝ := fun x => if x = 1 then 1 else f

/-- `p(n)`, the probability that the ALOHA channel unjams before the backlog increases, given a
backlog of `n` packets.  Kelly–Yudovina, p. 111, in the proof of Proposition 5.3. -/
noncomputable def alohaUnjamProb (ν f : ℝ) (n : ℕ) : ℝ :=
  (Real.exp (-ν) * (1 + ν) * (1 - f) ^ n + Real.exp (-ν) * (n : ℝ) * f * (1 - f) ^ (n - 1))
    / (1 - Real.exp (-ν) * (1 - (1 - f) ^ n - (n : ℝ) * f * (1 - f) ^ (n - 1)))

/-- The probability that exactly one transmission is attempted in an ALOHA slot with backlog `n`:
`e^{-ν} n f (1-f)^{n-1} + ν e^{-ν} (1-f)^n`.  Kelly–Yudovina, p. 110. -/
noncomputable def alohaSuccessProb (ν f : ℝ) (n : ℕ) : ℝ :=
  Real.exp (-ν) * ((n : ℝ) * f * (1 - f) ^ (n - 1)) + ν * Real.exp (-ν) * (1 - f) ^ n

end KellyStochasticNetworks
