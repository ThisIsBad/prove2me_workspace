import Mathlib
import Definitions.Def_PolicyGradTheory_ProjGA_MDP
import Definitions.Def_VectorSpaceOpt_pseudoinverse_predicate

namespace PolicyGradTheory.NPG

open FoundationsML.ReinforcementLearning

/-- The softmax parameterization (3) (arXiv:1908.00261v5, p. 10):
`π_θ(a|s) = exp(θ_{s,a}) / ∑_{a'} exp(θ_{s,a'})`, for `θ ∈ ℝ^{|S||A|}`. -/
noncomputable def softmaxPolicy {S A : Type*} [Fintype S] [Fintype A]
    (θ : EuclideanSpace ℝ (S × A)) : S → A → ℝ :=
  fun s a => Real.exp (θ (s, a)) / ∑ a', Real.exp (θ (s, a'))

/-- The score vector `∇_θ log π_θ(a|s) ∈ ℝ^{|S||A|}` (Euclidean gradient). -/
noncomputable def scoreVec {S A : Type*} [Fintype S] [Fintype A]
    (θ : EuclideanSpace ℝ (S × A)) (s : S) (a : A) : EuclideanSpace ℝ (S × A) :=
  gradient (fun θ' => Real.log (softmaxPolicy θ' s a)) θ

/-- The Fisher information matrix of (15) (p. 22):
`F_ρ(θ) = E_{s∼d^{π_θ}_ρ} E_{a∼π_θ(·|s)} [∇_θ log π_θ(a|s) (∇_θ log π_θ(a|s))^⊤]`. -/
noncomputable def fisher {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A]
    (P : S → A → S → ℝ) (γ : ℝ) (ρ : S → ℝ) (θ : EuclideanSpace ℝ (S × A)) :
    Matrix (S × A) (S × A) ℝ :=
  fun i j => ∑ s, PolicyGradTheory.ProjGA.visitation (softmaxPolicy θ) P γ ρ s *
    ∑ a, softmaxPolicy θ s a * scoreVec θ s a i * scoreVec θ s a j

/-- The Fisher matrix `F_ρ(θ)` as a (continuous) linear operator on `ℝ^{|S||A|}` with the
Euclidean norm, `w ↦ F_ρ(θ) w`. -/
noncomputable def fisherOp {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A]
    [DecidableEq A] (P : S → A → S → ℝ) (γ : ℝ) (ρ : S → ℝ) (θ : EuclideanSpace ℝ (S × A)) :
    EuclideanSpace ℝ (S × A) →L[ℝ] EuclideanSpace ℝ (S × A) :=
  LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin (fisher P γ ρ θ))

/-- The policy gradient `∇_θ V^{π_θ}(ρ)` of the softmax objective (Euclidean gradient). -/
noncomputable def valueGrad {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A]
    (P : S → A → S → ℝ) (r : S → A → ℝ) (γ : ℝ) (ρ : S → ℝ)
    (θ : EuclideanSpace ℝ (S × A)) : EuclideanSpace ℝ (S × A) :=
  gradient (fun θ' => PolicyGradTheory.ProjGA.valueAt (softmaxPolicy θ') P r γ ρ) θ

/-- A run of the NPG updates (15) (p. 22) with start distribution `ρ` and step size `η`:
for every `t`, `θ^{(t+1)} = θ^{(t)} + η F_ρ(θ^{(t)})^† ∇_θ V^{(t)}(ρ)`, where `F^†` is the
Moore–Penrose pseudoinverse, i.e. the minimum-norm least-squares pseudoinverse
`VectorSpaceOpt.IsPseudoinverse` (unique, so `∃` pins it). -/
def IsNPGRun {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A] [DecidableEq A]
    (P : S → A → S → ℝ) (r : S → A → ℝ) (γ : ℝ) (ρ : S → ℝ) (η : ℝ)
    (θ : ℕ → EuclideanSpace ℝ (S × A)) : Prop :=
  ∀ t : ℕ, ∃ B : EuclideanSpace ℝ (S × A) →L[ℝ] EuclideanSpace ℝ (S × A),
    VectorSpaceOpt.IsPseudoinverse (fisherOp P γ ρ (θ t)) B ∧
    θ (t + 1) = θ t + η • B (valueGrad P r γ ρ (θ t))

/-- The normalizer of Lemma 5.1 (p. 22) at parameter `θ`:
`Z(s) = ∑_a π_θ(a|s) exp(η A^{π_θ}(s,a)/(1−γ))`; `Z_t = npgNormalizer … (θ^{(t)})`. -/
noncomputable def npgNormalizer {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A]
    (P : S → A → S → ℝ) (r : S → A → ℝ) (γ η : ℝ) (θ : EuclideanSpace ℝ (S × A)) (s : S) : ℝ :=
  ∑ a, softmaxPolicy θ s a * Real.exp (η * PolicyGradTheory.ProjGA.advantage (softmaxPolicy θ) P r γ s a / (1 - γ))

/-- Footnote 6 (p. 22): every state is reachable from `ρ`, `∃ π, d^π_ρ(s) > 0`. -/
def AllReachable {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A]
    (P : S → A → S → ℝ) (γ : ℝ) (ρ : S → ℝ) : Prop :=
  ∀ s : S, ∃ π : S → A → ℝ, IsPolicy π ∧ 0 < PolicyGradTheory.ProjGA.visitation π P γ ρ s

end PolicyGradTheory.NPG
