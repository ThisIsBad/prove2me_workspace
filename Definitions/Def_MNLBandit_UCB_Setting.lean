import Mathlib
import Definitions.Def_ChoiceCDLP_MNL_mnlObjective

namespace MNLBandit.UCB

open ChoiceCDLP.MNL

/-- The MNL choice probabilities (2.1) of Agrawal–Avadhanula–Goyal–Zeevi (arXiv:1706.03880v2, p. 5)
with the normalization `v₀ = 1`. Products are `Fin N` (the paper's product `i` is index `i - 1`);
an outcome is `none` (the no-purchase alternative `0`) or `some i` (a purchase of `i`). When the
assortment `S` is offered, `none` has probability `1 / (1 + ∑_{j ∈ S} v_j)`, a product `i ∈ S` has
probability `v_i / (1 + ∑_{j ∈ S} v_j)`, and a product outside `S` has probability `0`. -/
noncomputable def choiceProb {N : ℕ} (v : Fin N → ℝ) (S : Finset (Fin N)) :
    Option (Fin N) → ℝ
  | none => 1 / (1 + ∑ j ∈ S, v j)
  | some i => if i ∈ S then v i / (1 + ∑ j ∈ S, v j) else 0

/-- The feasible family (2.3), p. 6: there are a totally unimodular integer matrix `A` (with `m`
rows) and an integer vector `b` such that `S ∈ 𝒮` iff the incidence vector `x(S)` satisfies
`A x(S) ≤ b`, i.e. `∑_{i ∈ S} A_{k i} ≤ b_k` for every row `k` (the bounds `0 ≤ x ≤ 1` hold for
every incidence vector). -/
def IsTU {N : ℕ} (𝒮 : Finset (Finset (Fin N))) : Prop :=
  ∃ (m : ℕ) (A : Matrix (Fin m) (Fin N) ℤ) (b : Fin m → ℤ), A.IsTotallyUnimodular ∧
    ∀ S : Finset (Fin N), S ∈ 𝒮 ↔ ∀ k : Fin m, ∑ i ∈ S, A k i ≤ b k

/-- Assumption 4.1.2, p. 11: `S ∈ 𝒮` and `Q ⊆ S` imply `Q ∈ 𝒮`. -/
def DownClosed {N : ℕ} (𝒮 : Finset (Finset (Fin N))) : Prop :=
  ∀ S ∈ 𝒮, ∀ Q ⊆ S, Q ∈ 𝒮

/-- The optimal expected revenue `R(S*, v) = max_{S ∈ 𝒮} R(S, v)` of (2.6), where
`R(S, v) = mnlObjective v r 1 S = ∑_{i ∈ S} r_i v_i / (1 + ∑_{j ∈ S} v_j)` is (2.2). The maximum is
over the nonempty finite family `𝒮`. -/
noncomputable def optRevenue {N : ℕ} (v r : Fin N → ℝ) (𝒮 : Finset (Finset (Fin N)))
    (h𝒮 : 𝒮.Nonempty) : ℝ :=
  𝒮.sup' h𝒮 (fun S => mnlObjective v r 1 S)

/-- A purchase history of horizon `T`: `h t` is the choice of customer `t` (0-based, the paper's
customer `t + 1`). -/
abbrev History (N T : ℕ) := Fin T → Option (Fin N)

/-- A deterministic nonanticipating assortment policy (2.4): the assortment offered to customer `t`
is a function of the choices of customers `0, …, t - 1` (the past assortments being themselves
functions of those choices). -/
abbrev Policy (N : ℕ) := (t : ℕ) → (Fin t → Option (Fin N)) → Finset (Fin N)

/-- The choices of the customers before `t` along the history `h`. -/
def histPrefix {N T : ℕ} (h : History N T) (t : Fin T) : Fin t.val → Option (Fin N) :=
  fun u => h (Fin.castLE t.isLt.le u)

/-- The assortment `S_t` offered to customer `t` along the history `h`. -/
def offered {N T : ℕ} (π : Policy N) (h : History N T) (t : Fin T) : Finset (Fin N) :=
  π t.val (histPrefix h t)

/-- The probability of the history `h` under the policy `π` and the MNL parameters `v`: given the
offered assortment, each customer chooses according to (2.1) independently of the past (p. 5), so
`ℙ_π(h) = ∏_t p_{h_t}(S_t)`. -/
noncomputable def histProb {N T : ℕ} (v : Fin N → ℝ) (π : Policy N) (h : History N T) : ℝ :=
  ∏ t : Fin T, choiceProb v (offered π h t) (h t)

open scoped Classical in
/-- The probability `ℙ_π(E)` of an event `E` on histories of horizon `T` (a finite sum). -/
noncomputable def probT {N : ℕ} (v : Fin N → ℝ) (π : Policy N) (T : ℕ)
    (E : History N T → Prop) : ℝ :=
  ∑ h : History N T, if E h then histProb v π h else 0

/-- The cumulative expected revenue (2.5), `𝔼_π ∑_{t=1}^T R(S_t, v)`. -/
noncomputable def expectedRevenue {N : ℕ} (v r : Fin N → ℝ) (π : Policy N) (T : ℕ) : ℝ :=
  ∑ h : History N T, histProb v π h * ∑ t : Fin T, mnlObjective v r 1 (offered π h t)

/-- The regret (2.6), p. 7: `Reg_π(T, v) = T · R(S*, v) − 𝔼_π ∑_{t=1}^T R(S_t, v)`. -/
noncomputable def regret {N : ℕ} (v r : Fin N → ℝ) (𝒮 : Finset (Finset (Fin N)))
    (h𝒮 : 𝒮.Nonempty) (π : Policy N) (T : ℕ) : ℝ :=
  (T : ℝ) * optRevenue v r 𝒮 h𝒮 - expectedRevenue v r π T

/-- `sel` is an argmax selector over `𝒮`: for every objective `f`, `sel f` is a member of `𝒮`
maximizing `f` over `𝒮`. It encodes an arbitrary tie-breaking rule for the argmax of (3.6). -/
def IsArgmaxSel {N : ℕ} (𝒮 : Finset (Finset (Fin N)))
    (sel : (Finset (Fin N) → ℝ) → Finset (Fin N)) : Prop :=
  ∀ f : Finset (Fin N) → ℝ, sel f ∈ 𝒮 ∧ ∀ S ∈ 𝒮, f S ≤ f (sel f)

end MNLBandit.UCB
