import Mathlib
import Definitions.Def_CHMSPricing_UnitDemand_SetSystem
import Definitions.Def_CHMSPricing_UnitDemand_MultiMechanism

namespace CHMSPricing.UnitDemand

variable {J : Type*} [Fintype J] [DecidableEq J] {m : ℕ}

open Classical in
/-- The services buyer `i` may buy when it arrives with `A` already allocated, at (reported)
values `v` and prices `p`: services `j ∈ Jᵢ` on its menu `J′ᵢ` (those with `A ∪ {j} ∈ 𝒥`) that
give nonnegative utility (`p_j ≤ v_j`) and maximise its utility `v_j − p_j` among those. -/
noncomputable def menuBest (𝒥 : SetSystem J) (owner : J → Fin m) (p v : J → ℝ)
    (A : Finset J) (i : Fin m) : Finset J :=
  let C := Finset.univ.filter (fun j => owner j = i ∧ 𝒥.Feasible (insert j A) ∧ p j ≤ v j)
  C.filter (fun j => ∀ j' ∈ C, v j' - p j' ≤ v j - p j)

/-- Buyer `i`'s choice from its price menu (proof of Theorem 4, p. 14): a utility-maximising
service among those with nonnegative utility, ties broken towards the least index under the
fixed enumeration `Fintype.equivFin J`; `none` (no purchase) if no service on the menu has
`p_j ≤ v_j`. -/
noncomputable def menuChoice (𝒥 : SetSystem J) (owner : J → Fin m) (p v : J → ℝ)
    (A : Finset J) (i : Fin m) : Option J :=
  if h : (menuBest 𝒥 owner p v A i).Nonempty then
    some ((Fintype.equivFin J).symm
      (((menuBest 𝒥 owner p v A i).image (Fintype.equivFin J)).min' (h.image _)))
  else none

/-- One step of the price-menu mechanism: buyer `i` arrives with `A` already allocated and the
service it chooses (if any) is added to `A`. -/
noncomputable def menuStep (𝒥 : SetSystem J) (owner : J → Fin m) (p v : J → ℝ)
    (A : Finset J) (i : Fin m) : Finset J :=
  match menuChoice 𝒥 owner p v A i with
  | some j => insert j A
  | none => A

/-- The set of services allocated by the price-menu mechanism with arrival order `σ`
(`σ 0` arrives first) and prices `p` at reported values `v`. -/
noncomputable def menuAlloc (𝒥 : SetSystem J) (owner : J → Fin m) (σ : Equiv.Perm (Fin m))
    (p v : J → ℝ) : Finset J :=
  (List.finRange m).foldl (fun A k => menuStep 𝒥 owner p v A (σ k)) ∅

/-- The (multi-dimensional) order-oblivious posted-price mechanism of the proof of Theorem 4
(§2.2, p. 5; App. B, p. 14): buyers arrive in the order `σ`; each buyer `i` is offered the
price menu `{p_j}_{j ∈ J′ᵢ}` over the services of `Jᵢ` that can still be feasibly allocated,
chooses a service (`menuChoice`), gets it and pays its price `p_j`; a buyer who buys nothing
pays `0`. -/
noncomputable def menuMech (𝒥 : SetSystem J) (owner : J → Fin m) (σ : Equiv.Perm (Fin m))
    (p : J → ℝ) : MultiMechanism J m where
  alloc v := menuAlloc 𝒥 owner σ p v
  pay v i := ∑ j ∈ (menuAlloc 𝒥 owner σ p v).filter (fun j => owner j = i), p j

/-- The feasibility constraint of Theorem 14 (§6.1, p. 9): `m` unit-demand buyers and items
`K`, with `cap k` copies of item `k`. A service is a pair `(i, k)` (buyer `i` gets a copy of
item `k`), and a set of services is feasible iff it uses at most `cap k` copies of each item `k`
and gives each buyer at most one service. It is the intersection of two partition matroids
on `Fin m × K` (by item, and by buyer). -/
def unitDemandSystem {K : Type*} [Fintype K] [DecidableEq K] (cap : K → ℕ) :
    SetSystem (Fin m × K) :=
  twoPartitionSystem Prod.snd cap Prod.fst (fun _ => 1)

end CHMSPricing.UnitDemand
