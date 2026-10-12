import Mathlib

namespace WagelmansELS.Efficient

/-- An economic lot sizing instance in Section 2. Only periods `1,...,n` are data. -/
structure Instance where
  n : ℕ
  d : ℕ → ℝ
  f : ℕ → ℝ
  c : ℕ → ℝ
  n_pos : 1 ≤ n
  d_nonneg : ∀ i, 1 ≤ i → i ≤ n → 0 ≤ d i
  d_last_pos : 0 < d n
  f_nonneg : ∀ i, 1 ≤ i → i ≤ n → 0 ≤ f i

namespace Instance
variable (P : Instance)

/-- Demand from `t` to `n`, with `D (n+1)=0`. -/
def D (t : ℕ) : ℝ := ∑ j ∈ Finset.Icc t P.n, P.d j

/-- Cost of a setup at `i` followed by the next setup at `t`. -/
def setupCost (i t : ℕ) (later : ℕ → ℝ) : ℝ :=
  P.f i + P.c i * (P.D i - P.D t) + later t

/-- Backward dynamic-programming table. Stage `m` has computed the last `m` periods. -/
noncomputable def Gtable : ℕ → ℕ → ℝ
  | 0 => fun _ => 0
  | m + 1 =>
      let i := P.n - m
      let old := Gtable m
      let positiveCost := (Finset.Ioc i (P.n + 1)).inf'
        (by simp; omega) (fun t => P.setupCost i t old)
      let value := if 0 < P.d i then positiveCost
        else min (old (i + 1))
          (if h : (Finset.Ioc (i + 1) (P.n + 1)).Nonempty then
            (Finset.Ioc (i + 1) (P.n + 1)).inf' h (fun t => P.setupCost i t old)
           else old (i + 1))
      fun t => if t = i then value else old t

/-- The backward value `G`, including sentinel `G(n+1)=0`. -/
noncomputable def G (t : ℕ) : ℝ := P.Gtable P.n t

/-- The quantity minimized in the threshold rule, with setup cost omitted. -/
noncomputable def score (i t : ℕ) : ℝ := P.c i * (P.D i - P.D t) + P.G t

end Instance
end WagelmansELS.Efficient
