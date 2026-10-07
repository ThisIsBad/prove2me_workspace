import Mathlib
import Definitions.Def_Gomory69_Lifting_GroupPolyhedron

namespace Gomory69.Lifting

variable {G H : Type*} [AddCommGroup G] [AddCommGroup H]

/-- The lifted coefficients of THEOREM 19: `π(g) = π′(ψ g)` for `g ∈ 𝒢⁺`, with `π′(0̄) = 0`,
so `π(g) = 0` on the kernel of `ψ`. -/
def liftCoeff [DecidableEq H] (ψ : G →+ H) (π' : Plus H → ℝ) : Plus G → ℝ :=
  fun g => ext π' (ψ g)

/-- Pushing a path forward along `ψ` (proof of THEOREM 19, p. 486):
`τ(h) = ∑_{g ∈ ψ⁻¹ h} t(g)` for `h ∈ ℋ⁺`. -/
def pushForward [Fintype G] [DecidableEq G] [DecidableEq H] (ψ : G →+ H)
    (t : Plus G → ℕ) : Plus H → ℕ :=
  fun h => ∑ g ∈ Finset.univ.filter (fun g : Plus G => ψ (g : G) = (h : H)), t g

/-- The non-kernel part of the lifted path `T_k(τ)` (p. 487): for `g ∈ 𝒢⁺` with `ψ g = h ≠ 0̄`,
written `g = φ(h) + k′`, it is `τ(h)` if `k′ = k` and `0` otherwise; it is `0` on the kernel. -/
def liftedPathBase [DecidableEq G] [DecidableEq H] (ψ : G →+ H) (φ : H → G) (k : G)
    (τ : Plus H → ℕ) : Plus G → ℕ :=
  fun g => if hg : ψ (g : G) = 0 then 0
    else if (g : G) = φ (ψ (g : G)) + k then τ ⟨ψ (g : G), hg⟩ else 0

/-- The kernel element that closes the lifted path: `g₀ − ∑_{g ∉ 𝒦} t_k(g) · g`. -/
def closingElement [Fintype G] [DecidableEq G] [DecidableEq H] (ψ : G →+ H) (φ : H → G)
    (g₀ k : G) (τ : Plus H → ℕ) : G :=
  g₀ - ∑ g : Plus G, liftedPathBase ψ φ k τ g • (g : G)

/-- The lifted path `T_k(τ)` of p. 487: the non-kernel part `liftedPathBase`, plus a single `1` on
the closing kernel element `g₀ − ∑_{g ∉ 𝒦} t_k(g) · g` when that element is nonzero (when it is
`0̄`, nothing is added, since `t` has no `0̄` coordinate). -/
def liftedPath [Fintype G] [DecidableEq G] [DecidableEq H] (ψ : G →+ H) (φ : H → G)
    (g₀ k : G) (τ : Plus H → ℕ) : Plus G → ℕ :=
  fun g => liftedPathBase ψ φ k τ g +
    if (g : G) = closingElement ψ φ g₀ k τ then 1 else 0

end Gomory69.Lifting
