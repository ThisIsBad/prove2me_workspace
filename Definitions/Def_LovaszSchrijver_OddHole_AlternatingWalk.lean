import Mathlib

namespace LovaszSchrijver.OddHole

/-- `v₀, v₁, …, v_p` is a walk in `H`: consecutive vertices are adjacent. -/
def IsWalkSeq {W : Type} (H : SimpleGraph W) {p : ℕ} (v : Fin (p + 1) → W) : Prop :=
  ∀ t : Fin p, H.Adj (v t.castSucc) (v t.succ)

/-- The alternating sum `b(v₀v₁) − a(v₁v₂) + b(v₂v₃) − ⋯` along the walk (p. 178):
the `t`-th edge (counting from `0`) contributes `b` if `t` is even and `−a` if `t` is odd. -/
def altB {W : Type} (a b : Sym2 W → ℝ) {p : ℕ} (v : Fin (p + 1) → W) : ℝ :=
  ∑ t : Fin p, if Even t.val then b s(v t.castSucc, v t.succ) else -a s(v t.castSucc, v t.succ)

/-- The alternating sum `−a(v₀v₁) + b(v₁v₂) − a(v₂v₃) + ⋯` along the walk (p. 178):
the `t`-th edge contributes `−a` if `t` is even and `b` if `t` is odd. -/
def altA {W : Type} (a b : Sym2 W → ℝ) {p : ℕ} (v : Fin (p + 1) → W) : ℝ :=
  ∑ t : Fin p, if Even t.val then -a s(v t.castSucc, v t.succ) else b s(v t.castSucc, v t.succ)

end LovaszSchrijver.OddHole
