import Mathlib

namespace SionMinimax.KneserFan

/-- Sion 1958, Definition 2.1, p. 172 (after K. Fan): `f` is concavelike in `M` if for every
`μ₁ μ₂ ∈ M` and `0 ≤ t ≤ 1` there is a single `μ ∈ M` with
`t f(μ₁, ν) + (1 - t) f(μ₂, ν) ≤ f(μ, ν)` for all `ν ∈ N`. -/
def Concavelike {M N : Type*} (f : M → N → ℝ) : Prop :=
  ∀ μ₁ μ₂ : M, ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
    ∃ μ : M, ∀ ν : N, t * f μ₁ ν + (1 - t) * f μ₂ ν ≤ f μ ν

/-- Sion 1958, Definition 2.2, p. 172 (after K. Fan): `f` is convexlike in `N` if for every
`ν₁ ν₂ ∈ N` and `0 ≤ t ≤ 1` there is a single `ν ∈ N` with
`t f(μ, ν₁) + (1 - t) f(μ, ν₂) ≥ f(μ, ν)` for all `μ ∈ M`. -/
def Convexlike {M N : Type*} (f : M → N → ℝ) : Prop :=
  ∀ ν₁ ν₂ : N, ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
    ∃ ν : N, ∀ μ : M, f μ ν ≤ t * f μ ν₁ + (1 - t) * f μ ν₂

/-- Sion 1958, Definition 2.3, p. 172: `f` is concave-convexlike if it is concavelike in `M`
and convexlike in `N`. -/
def ConcaveConvexlike {M N : Type*} (f : M → N → ℝ) : Prop :=
  Concavelike f ∧ Convexlike f

/-- Sion 1958, Definition 2.8, p. 172: `sup inf f = sup_{μ ∈ M} inf_{ν ∈ N} f(μ, ν)`, computed in
the extended reals (the empty supremum is `⊥`, the empty infimum is `⊤`). -/
noncomputable def supInf {M N : Type*} (f : M → N → ℝ) : EReal :=
  ⨆ μ : M, ⨅ ν : N, ((f μ ν : ℝ) : EReal)

/-- Sion 1958, Definition 2.8, p. 172: `inf sup f = inf_{ν ∈ N} sup_{μ ∈ M} f(μ, ν)`, computed in
the extended reals. -/
noncomputable def infSup {M N : Type*} (f : M → N → ℝ) : EReal :=
  ⨅ ν : N, ⨆ μ : M, ((f μ ν : ℝ) : EReal)

end SionMinimax.KneserFan
