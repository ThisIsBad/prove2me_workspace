import Mathlib
import Definitions.Def_InventoryControl_newsboy
import Definitions.Def_FoundationsML_Stability_EmpiricalError
import Definitions.Def_FoundationsML_Stability_GeneralizationError
import Definitions.Def_StabGen_RKHS_Regularization

namespace BigDataNV.Reg

/-- The newsvendor cost (2), p. 5: `C(q; d) = b (d − q)⁺ + h (q − d)⁺`, with unit backordering
cost `b` and unit holding cost `h`. It is the published `newsboyLoss` with overage cost `co = h`
and underage cost `cu = b`. -/
noncomputable def nvCost (b h : ℝ) : ℝ → ℝ → ℝ :=
  fun q d => InventoryControl.newsboyLoss h b q d

/-- A linear decision rule, §2.3, p. 6: the vector `q ∈ ℝᵖ` acts on a feature vector `x` by
`q(x) = qᵀx = ∑ⱼ qʲ xʲ`. -/
noncomputable def linEval {p : ℕ} : EuclideanSpace ℝ (Fin p) → EuclideanSpace ℝ (Fin p) → ℝ :=
  fun g x => inner ℝ g x

/-- The objective of (NV-reg), §2.5, p. 7: `R̂(q; Sₙ) + λ‖q‖₂²`. -/
noncomputable def nvRegObjective {p n : ℕ} (b h lam : ℝ)
    (S : Fin n → EuclideanSpace ℝ (Fin p) × ℝ) (q : EuclideanSpace ℝ (Fin p)) : ℝ :=
  StabGen.RKHS.regRisk (nvCost b h) linEval S lam (fun g => ‖g‖ ^ 2) q

/-- `q` solves (NV-reg) on the sample `S`: it minimizes `R̂(·; Sₙ) + λ‖·‖₂²` over all of `ℝᵖ`. -/
def IsNVRegSolution {p n : ℕ} (b h lam : ℝ)
    (S : Fin n → EuclideanSpace ℝ (Fin p) × ℝ) (q : EuclideanSpace ℝ (Fin p)) : Prop :=
  ∀ g : EuclideanSpace ℝ (Fin p), nvRegObjective b h lam S q ≤ nvRegObjective b h lam S g

/-- The leave-one-out objective of the stability argument (App. B, Theorems 4 and 5): the `i`-th
data term is dropped and the weight `1/n` is kept,
`(1/n) ∑_{j ≠ i} C(qᵀxⱼ; dⱼ) + λ‖q‖₂²`. -/
noncomputable def nvRegLooObjective {p n : ℕ} (b h lam : ℝ)
    (S : Fin n → EuclideanSpace ℝ (Fin p) × ℝ) (i : Fin n) (q : EuclideanSpace ℝ (Fin p)) : ℝ :=
  StabGen.RKHS.truncRegRisk (nvCost b h) linEval S i lam (fun g => ‖g‖ ^ 2) q

/-- `q` minimizes the leave-one-out objective `nvRegLooObjective b h lam S i` over `ℝᵖ`. -/
def IsNVRegLooSolution {p n : ℕ} (b h lam : ℝ)
    (S : Fin n → EuclideanSpace ℝ (Fin p) × ℝ) (i : Fin n) (q : EuclideanSpace ℝ (Fin p)) : Prop :=
  ∀ g : EuclideanSpace ℝ (Fin p), nvRegLooObjective b h lam S i q ≤ nvRegLooObjective b h lam S i g

/-- The data support `X × D` of §3, p. 9, with `D = [0, D̄]`. -/
def dataSupport {p : ℕ} (Xdom : Set (EuclideanSpace ℝ (Fin p))) (Dbar : ℝ) :
    Set (EuclideanSpace ℝ (Fin p) × ℝ) :=
  Xdom ×ˢ Set.Icc 0 Dbar

end BigDataNV.Reg
