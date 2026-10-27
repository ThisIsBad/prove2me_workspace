import Mathlib

namespace AssemblyCoord.Feedback

/-- Parameters, §3 (p. 7): `M` contractors, `N` periods (= feedback periods, §3.1), total effort
bounds `qlo` (q̲, the minimum) and `qhi` (q̄, the maximum), the OEM's effort target `qstar` (q*),
marginal benefit `p`, contractor share `γ`, marginal effort cost `c`. -/
structure Params where
  M : ℕ
  N : ℕ
  qlo : ℝ
  qhi : ℝ
  qstar : ℝ
  p : ℝ
  γ : ℝ
  c : ℝ

/-- The standing assumptions of §3 (pp. 6–7): at least one contractor and one period,
`q̄ > q* > q̲ ≥ 0`, and positive `p`, `γ`, `c`. -/
def Params.Standing (P : Params) : Prop :=
  1 ≤ P.M ∧ 1 ≤ P.N ∧ 0 ≤ P.qlo ∧ P.qlo < P.qstar ∧ P.qstar < P.qhi ∧
  0 < P.p ∧ 0 < P.γ ∧ 0 < P.c

/-- A history: the effort profiles of the periods played so far, oldest first. Under the
information-feedback mechanism every contractor observes it before choosing the current
period's effort. -/
abbrev History (M : ℕ) := List (Fin M → ℝ)

/-- A pure history-dependent strategy profile: `σ i h` is contractor `i`'s effort in the current
period after history `h`. -/
abbrev Profile (M : ℕ) := Fin M → History M → ℝ

/-- Per-period effort range `[q̲/N, q̄/N]` (p. 7). -/
def Params.FeasibleEffort (P : Params) (e : ℝ) : Prop :=
  P.qlo / P.N ≤ e ∧ e ≤ P.qhi / P.N

/-- A strategy is feasible when it prescribes a feasible effort after every history. -/
def Params.FeasibleStrategy (P : Params) (s : History P.M → ℝ) : Prop :=
  ∀ h, P.FeasibleEffort (s h)

/-- A history at which the contractors still move (fewer than `N` periods played) and whose past
efforts are all feasible. -/
def Params.FeasibleHistory (P : Params) (h : History P.M) : Prop :=
  h.length < P.N ∧ ∀ a ∈ h, ∀ i, P.FeasibleEffort (a i)

/-- `k` further periods of play of `σ` after history `h`. -/
def play {M : ℕ} (σ : Profile M) : History M → ℕ → History M
  | h, 0 => h
  | h, k + 1 => play σ (h ++ [fun i => σ i h]) k

/-- Cumulative effort level `q̂_i` after history `h`, from initial levels `q0`
(`q0 = 0` in the main model). -/
def level {M : ℕ} (q0 : Fin M → ℝ) (h : History M) (i : Fin M) : ℝ :=
  q0 i + (h.map (fun a => a i)).sum

/-- Final levels `q̂_N` when `σ` is played from history `h` to the end of period `N`. -/
def Params.final (P : Params) (q0 : Fin P.M → ℝ) (σ : Profile P.M) (h : History P.M) :
    Fin P.M → ℝ :=
  level q0 (play σ h (P.N - h.length))

/-- Project effort level `q_min = min_i q̂_{i,N}`. -/
noncomputable def projectLevel {M : ℕ} (x : Fin M → ℝ) : ℝ := ⨅ j, x j

/-- Contractor `i`'s profit (2), `γ S(q_min) − c q̂_{i,N}`, with the OEM payoff (1)
`S(q_min) = p min{q_min, q*}`, as a function of the final level vector `x`. -/
noncomputable def Params.profit (P : Params) (x : Fin P.M → ℝ) (i : Fin P.M) : ℝ :=
  P.γ * (P.p * min (projectLevel x) P.qstar) - P.c * x i

/-- Subgame-perfect equilibrium: every strategy is feasible, and at every feasible history no
contractor gains by switching to any feasible strategy. -/
def Params.IsSPE (P : Params) (q0 : Fin P.M → ℝ) (σ : Profile P.M) : Prop :=
  (∀ i, P.FeasibleStrategy (σ i)) ∧
  ∀ h, P.FeasibleHistory h → ∀ (i : Fin P.M) (τ : History P.M → ℝ), P.FeasibleStrategy τ →
    P.profit (P.final q0 (Function.update σ i τ) h) i ≤ P.profit (P.final q0 σ h) i

/-- The history after the first `n` periods of `σ`'s own path. -/
def pathHist {M : ℕ} (σ : Profile M) (n : ℕ) : History M := play σ [] n

/-- `Ê_{n:N}` at history `h`: the final level vectors of all SPEs continued from `h`. -/
def Params.SPEOutcomes (P : Params) (q0 : Fin P.M → ℝ) (h : History P.M) :
    Set (Fin P.M → ℝ) :=
  {x | ∃ σ', P.IsSPE q0 σ' ∧ P.final q0 σ' h = x}

/-- The inner "min" of (24): contractor `i`'s worst profit when its own final level is `y` and
the other contractors' final levels range over their components of the SPE outcomes at `h`. -/
noncomputable def Params.secureValue (P : Params) (q0 : Fin P.M → ℝ) (h : History P.M)
    (i : Fin P.M) (y : ℝ) : ℝ :=
  sInf ((fun x => P.profit (Function.update x i y) i) '' P.SPEOutcomes q0 h)

/-- Definition 2 (SPSE): an SPE such that, at the start of every period along its own path,
each contractor's own final level maximizes the secure value (24) over its components of the
SPE outcomes of that subgame. -/
def Params.IsSPSE (P : Params) (q0 : Fin P.M → ℝ) (σ : Profile P.M) : Prop :=
  P.IsSPE q0 σ ∧ ∀ n, n < P.N → ∀ i : Fin P.M,
    ∀ y ∈ (fun x => x i) '' P.SPEOutcomes q0 (pathHist σ n),
      P.secureValue q0 (pathHist σ n) i y ≤
        P.secureValue q0 (pathHist σ n) i (P.final q0 σ (pathHist σ n) i)

end AssemblyCoord.Feedback
