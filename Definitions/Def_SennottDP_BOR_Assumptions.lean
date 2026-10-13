import Mathlib
import Definitions.Def_SennottDP_BOR_FirstPassage

open scoped ENNReal NNReal

namespace SennottDP.BOR

variable {S : Type} [Countable S] {Act : Type}

/-- The states at which some action costs at most `U`: `{i | C(i,a) ≤ U for some a ∈ A_i}`.
With `U = J_d + ε` this is the set `D` of (BOR2), p. 145; with a real `U > 0` it is the set
`D_U` of (CAV2), p. 148. -/
def lowCostSet (M : SennottDP.Discounted.MDC S Act) (U : ℝ≥0∞) : Set S :=
  {i | ∃ a ∈ M.A i, (M.C i a : ℝ≥0∞) ≤ U}

/-- Sennott (1999), Theorem 7.5.6(ii), p. 145: for a stationary policy `e`, the set
`D(e) = {i | C(i,e) ≤ U}` (used with `U = J + ε`). -/
def lowCostSetOf (M : SennottDP.Discounted.MDC S Act) (e : StationaryPolicy M) (U : ℝ≥0∞) : Set S :=
  {i | (M.C i (e.1 i) : ℝ≥0∞) ≤ U}

/-- The positive recurrent class `R_d` of a `z` standard policy `d`: the communicating class of
`z` in the Markov chain induced by `d` (Proposition C.2.6(i), p. 301: a `z` standard chain
consists of one positive recurrent class containing `z` and transient states). -/
def recClass (M : SennottDP.Discounted.MDC S Act) (d : RandStationaryPolicy M) (z : S) : Set S :=
  commClass d.toPolicy z

/-- Sennott (1999), Theorem 7.5.6, p. 145: the (BOR) assumptions for the distinguished state
`z`, the (randomized) stationary policy `d` and the constant `ε`:
* (BOR1) `d` is a `z` standard policy, with positive recurrent class `R_d`;
* (BOR2) `ε > 0` and `D = {i | C(i,a) ≤ J_d + ε for some a}` is finite, where `J_d` is the
  (constant) average cost of `d`, written here as its value `J_d(z)`;
* (BOR3) for every `i ∈ D − R_d` there is a policy `θ_i ∈ ℜ*(z, i)`. -/
def BORAssumptions (M : SennottDP.Discounted.MDC S Act) (z : S) (d : RandStationaryPolicy M) (ε : ℝ) : Prop :=
  IsZStandard d.toPolicy z ∧
  (0 < ε ∧ (lowCostSet M (avgCost d.toPolicy z + ENNReal.ofReal ε)).Finite) ∧
  ∀ i ∈ lowCostSet M (avgCost d.toPolicy z + ENNReal.ofReal ε) \ recClass M d z,
    ∃ θ : SennottDP.Discounted.Policy M, InRStar θ z {i}

/-- Sennott (1999), Corollary 7.5.9, p. 148: the (CAV) assumptions for `z` and `d`:
* (CAV1) = (BOR1): `d` is a `z` standard policy with positive recurrent class `R_d`;
* (CAV2) for every `U > 0` the set `D_U = {i | C(i,a) ≤ U for some a}` is finite;
* (CAV3) for every `i ∈ S − R_d` there is a policy `θ_i ∈ ℜ*(z, i)`. -/
def CAVAssumptions (M : SennottDP.Discounted.MDC S Act) (z : S) (d : RandStationaryPolicy M) : Prop :=
  IsZStandard d.toPolicy z ∧
  (∀ U : ℝ, 0 < U → (lowCostSet M (ENNReal.ofReal U)).Finite) ∧
  ∀ i ∉ recClass M d z, ∃ θ : SennottDP.Discounted.Policy M, InRStar θ z {i}

end SennottDP.BOR
