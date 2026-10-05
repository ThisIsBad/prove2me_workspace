import Mathlib
import Definitions.Def_ProcessingNetworks_PacketNetworks_RPSRawModel
import Definitions.Def_ProcessingNetworks_PacketNetworks_ProcessesAndFluidModel

namespace ProcessingNetworks.PacketNetworks

open MeasureTheory Filter

/-- `ŝ^z_i(τ) = E[s^z_i(τ) | Z^z(τ−1)]` (Section 12.7, before (12.62)): since `s(τ) = f(Z(τ−1),
U(τ))` with `U(τ)` uniform on `(0,1)` and independent of `Z(τ−1)`, this is
`∫₀¹ f(Z^z(τ−1), u)_i du`. -/
noncomputable def shat {I K : ℕ} {Ω : Type*} (fr : FixedRoutingData I K)
    (P : PacketPrimitives I I Ω) (z : Fin I → ℕ) (i : Fin I) (τ : ℕ) (ω : Ω) : ℝ :=
  ∫ uu in Set.Ioo (0 : ℝ) 1,
    (P.f (fun i' => (policyState fr.dat P z (τ - 1) ω i').toNat) uu i : ℝ)

/-- The class-level residual process `ξ^z_i(τ,ω) := ∑_{m=1}^{τ} (s^z_i(m,ω) − ŝ^z_i(m,ω))`,
Dai & Harrison p. 250 (PDF p. 266), for the network started at `z` under the policy of `P`. -/
noncomputable def xi {I K : ℕ} {Ω : Type*} (fr : FixedRoutingData I K)
    (P : PacketPrimitives I I Ω) (z : Fin I → ℕ) (i : Fin I) (τ : ℕ) (ω : Ω) : ℝ :=
  ∑ m ∈ Finset.Icc 1 τ, ((policySched fr.dat P z m ω i : ℝ) - shat fr P z i m ω)

/-- `Ω₂` (Lemma 12.23): for the sequence `zseq` of initial states, the set of sample paths on
which `ξ^{zₗ}(|zₗ|,ω)/|zₗ| → 0` as `ℓ → ∞` (componentwise). The index `ℓ` is 0-based (`zseq 0`
playing the book's `z₁`). -/
def omega2 {I K : ℕ} {Ω : Type*} (fr : FixedRoutingData I K) (P : PacketPrimitives I I Ω)
    (zseq : ℕ → Fin I → ℕ) : Set Ω :=
  {ω | ∀ i : Fin I,
    Tendsto (fun ℓ => xi fr P (zseq ℓ) i ⌊sizeN (zseq ℓ)⌋₊ ω / sizeN (zseq ℓ)) atTop (nhds 0)}

end ProcessingNetworks.PacketNetworks
