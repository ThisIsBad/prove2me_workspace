import Mathlib
import Definitions.Def_MultPacing_Existence_Model

namespace MultPacing.Existence

variable {N G : Type*} [Fintype N] [DecidableEq N] [Fintype G]

/-- Bids on good `j` in the `ε`-smoothed game (Definition 3, p. 11). The bidders are `Option N`:
`some i` is buyer `i`, bidding `α_i v_ij`, and `none` is the artificial reserve bidder, bidding `2ε`
("treated as one of the buyers"). -/
def smBid (P : PacingGame N G) (ε : ℝ) (α : N → ℝ) (j : G) : Option N → ℝ
  | none => 2 * ε
  | some i => α i * P.v i j

/-- The highest bid `b*_j` on good `j`, the reserve bid included. -/
noncomputable def topBid (P : PacingGame N G) (ε : ℝ) (α : N → ℝ) (j : G) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (smBid P ε α j)

/-- The band weight `max(0, b_k − (b*_j − ε))` of bidder `k` on good `j`; it is positive exactly for
the bidders strictly inside the band `S_j = {k : b_k ≥ b*_j − ε}` and `0` outside `S_j`. -/
noncomputable def bandWeight (P : PacingGame N G) (ε : ℝ) (α : N → ℝ) (j : G) (k : Option N) : ℝ :=
  max 0 (smBid P ε α j k - (topBid P ε α j - ε))

/-- The fraction `x_ij` of good `j` won by buyer `i` in the smoothed game: its band weight divided by
the sum of the band weights of all bidders in `S_j`, the reserve bidder included. -/
noncomputable def smAlloc (P : PacingGame N G) (ε : ℝ) (α : N → ℝ) (i : N) (j : G) : ℝ :=
  bandWeight P ε α j (some i) / ∑ k : Option N, bandWeight P ε α j k

/-- The per-unit price `p_ij` buyer `i` pays for good `j` in the smoothed game: the highest bid on
`j` among the bidders other than `i` (the reserve bidder included), minus `ε`. -/
noncomputable def smPrice (P : PacingGame N G) (ε : ℝ) (α : N → ℝ) (i : N) (j : G) : ℝ :=
  (Finset.univ.erase (some i)).sup' ⟨none, by simp⟩ (smBid P ε α j) - ε

/-- The payment `s_ij = x_ij p_ij` of buyer `i` for good `j` in the smoothed game. -/
noncomputable def smPay (P : PacingGame N G) (ε : ℝ) (α : N → ℝ) (i : N) (j : G) : ℝ :=
  smAlloc P ε α i j * smPrice P ε α i j

/-- Total spend `α_i ε + ∑_j s_ij` of buyer `i`, the artificial good included. -/
noncomputable def smSpend (P : PacingGame N G) (ε : ℝ) (α : N → ℝ) (i : N) : ℝ :=
  α i * ε + ∑ j, smPay P ε α i j

/-- The leftover-budget term of the smoothed utility: `y` if `y ≥ 0` (budget not exceeded) and
`H y` if `y < 0` (budget exceeded). -/
noncomputable def budgetTerm (H y : ℝ) : ℝ :=
  if 0 ≤ y then y else H * y

/-- Utility of buyer `i` in the `(ε, H)`-smoothed pacing game:
`(B_i − α_i ε − ∑_j s_ij) + 2 α_i ε + ∑_j x_ij v_ij` if she does not exceed her budget, and
`H (B_i − α_i ε − ∑_j s_ij) + 2 α_i ε + ∑_j x_ij v_ij` if she exceeds it. -/
noncomputable def smUtility (P : PacingGame N G) (ε H : ℝ) (α : N → ℝ) (i : N) : ℝ :=
  budgetTerm H (P.B i - smSpend P ε α i) + 2 * α i * ε + ∑ j, smAlloc P ε α i j * P.v i j

/-- A pure-strategy Nash equilibrium of the `(ε, H)`-smoothed pacing game: every multiplier lies in
`[0,1]` and no buyer gains by changing her own multiplier within `[0,1]`. -/
def IsSmoothedPNE (P : PacingGame N G) (ε H : ℝ) (α : N → ℝ) : Prop :=
  (∀ i, α i ∈ Set.Icc (0 : ℝ) 1) ∧
    ∀ i, ∀ a ∈ Set.Icc (0 : ℝ) 1, smUtility P ε H (Function.update α i a) i ≤ smUtility P ε H α i

end MultPacing.Existence
