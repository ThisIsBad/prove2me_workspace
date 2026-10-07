import Mathlib
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_ProjSchedTW_Complexity_Encoding

namespace KarpPapadimitriou.Generator

abbrev Sym := ProjSchedTW.Complexity.BSym

/-- A binary string followed by a separator. -/
def encZ (z : List Bool) : List Sym :=
  z.map (fun b => if b then ProjSchedTW.Complexity.BSym.one else ProjSchedTW.Complexity.BSym.zero) ++
    [ProjSchedTW.Complexity.BSym.sep]

/-- A dimension-check input consists of `z` and a bit string `y`. -/
def encZY (z y : List Bool) : List Sym := encZ z ++ encZ y

/-- A point with integer coordinates, in binary. -/
def encZX {n : ℕ} (z : List Bool) (x : Fin n → ℤ) : List Sym :=
  encZ z ++ ProjSchedTW.Complexity.encNat n ++
    ProjSchedTW.Complexity.encInts (List.ofFn x)

/-- A threshold instance `⟨z,c,k⟩`. -/
def encDInput {n : ℕ} (z : List Bool) (c : Fin n → ℤ) (k : ℤ) : List Sym :=
  encZX z c ++ ProjSchedTW.Complexity.encInt k

/-- A triple `⟨z,f,g⟩` describing the inequality `f·x ≤ g`. -/
def encTriple {n : ℕ} (z : List Bool) (f : Fin n → ℤ) (g : ℤ) : List Sym :=
  encZX z f ++ ProjSchedTW.Complexity.encInt g

/-- Definition 1: the feasible integer vectors have nonnegative coordinates, and the three
languages displayed across pp. 3–4 are decidable in polynomial time. -/
structure COP where
  L : Set (List Bool)
  n : List Bool → ℕ
  S : (z : List Bool) → Set (Fin (n z) → ℤ)
  nonnegative : ∀ z ∈ L, ∀ x ∈ S z, ∀ j, 0 ≤ x j
  L_poly : {w : List Sym | ∃ z ∈ L, w = encZ z} ∈ CookPvsNP.P Sym
  dimension_poly :
    {w : List Sym | ∃ (z : List Bool) (y : List Bool),
      z ∈ L ∧ y.length = n z ∧ w = encZY z y} ∈ CookPvsNP.P Sym
  feasible_poly :
    {w : List Sym | ∃ (z : List Bool) (x : Fin (n z) → ℤ),
      z ∈ L ∧ x ∈ S z ∧ w = encZX z x} ∈ CookPvsNP.P Sym

/-- The paper's rational convex hull of feasible integer vectors. -/
def hull (C : COP) (z : List Bool) : Set (Fin (C.n z) → ℚ) :=
  convexHull ℚ ((fun x : Fin (C.n z) → ℤ => fun i => (x i : ℚ)) '' C.S z)

/-- Integer coefficient vector evaluated at a rational point. -/
def dotQ {n : ℕ} (f : Fin n → ℤ) (x : Fin n → ℚ) : ℚ :=
  ∑ i : Fin n, (f i : ℚ) * x i

/-- Integer coefficient vector evaluated at an integer point. -/
def dotZ {n : ℕ} (f x : Fin n → ℤ) : ℤ :=
  ∑ i : Fin n, f i * x i

/-- The decision language `D(C)`, restricted to well-formed instance codes. -/
def DLang (C : COP) : CookPvsNP.Lang Sym :=
  {w | ∃ (z : List Bool) (c : Fin (C.n z) → ℤ) (k : ℤ),
    z ∈ C.L ∧ (∃ x ∈ C.S z, k ≤ dotZ c x) ∧ w = encDInput z c k}

/-- The dependent type of triples `⟨z,f,g⟩`. -/
abbrev Triple (C : COP) := Σ z : List Bool, (Fin (C.n z) → ℤ) × ℤ

/-- A facial description has only valid first components and characterizes the hull for every
valid instance and every rational test point. -/
def IsFacialDescription (C : COP) (F : Set (Triple C)) : Prop :=
  (∀ a ∈ F, a.1 ∈ C.L) ∧
  ∀ z ∈ C.L, ∀ x : Fin (C.n z) → ℚ,
    x ∈ hull C z ↔ ∀ f g, (⟨z, (f, g)⟩ : Triple C) ∈ F → dotQ f x ≤ (g : ℚ)

/-- A single exponent bounds every coefficient of every inequality in the family. -/
def IsSmall (C : COP) (F : Set (Triple C)) : Prop :=
  ∃ k : ℕ, ∀ a ∈ F,
    (∀ i, (a.2.1 i).natAbs ≤ 2 ^ ((a.1.length + C.n a.1) ^ k + k)) ∧
      a.2.2.natAbs ≤ 2 ^ ((a.1.length + C.n a.1) ^ k + k)

end KarpPapadimitriou.Generator
