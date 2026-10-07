import Mathlib

namespace QueueingFundamentals.Transient

/-- The modified Bessel function of the first kind of nonnegative integer order `n`, given by the
book's series (p.101): `I_n(y) = ∑_{k ≥ 0} (y/2)^{n+2k} / (k! (n+k)!)`. -/
noncomputable def besselI (n : ℕ) (y : ℝ) : ℝ :=
  ∑' k : ℕ, (y / 2) ^ (n + 2 * k) / ((Nat.factorial k : ℝ) * (Nat.factorial (n + k) : ℝ))

/-- The modified Bessel function of integer order, with the standard convention `I_{-m} = I_m`
for `m ∈ ℕ`; (2.75) needs this for the index `n - i` when `n < i`. -/
noncomputable def besselIZ (m : ℤ) (y : ℝ) : ℝ :=
  besselI m.natAbs y

end QueueingFundamentals.Transient
