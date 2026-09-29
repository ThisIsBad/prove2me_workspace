import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Dynamics.Flow
import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.Maps.Basic

namespace BirkhoffGlobalSection

noncomputable section

open scoped ContDiff

/-- Four real coordinates, ordered as `(q₁,q₂,p₁,p₂)` for the Jacobi Hamiltonian
and as `(z₁,z₂,w₁,w₂)` after Levi-Civita regularization. -/
abbrev Phase := Fin 4 → ℝ

/-- Two real coordinates, used for the parameter disk of a global section. -/
abbrev Plane := Fin 2 → ℝ

def qNormSq (s : Phase) : ℝ := s 0 ^ 2 + s 1 ^ 2

def zNormSq (s : Phase) : ℝ := s 0 ^ 2 + s 1 ^ 2

def wNormSq (s : Phase) : ℝ := s 2 ^ 2 + s 3 ^ 2

/-- The totalized real-valued extension of Equation (1.1) of Joung--van Koert.
It agrees with the planar circular restricted three-body Hamiltonian on the
collision-free domain (and the source's physical range `0 ≤ μ ≤ 1`). -/
def jacobiHamiltonian (μ : ℝ) (s : Phase) : ℝ :=
  (s 2 ^ 2 + s 3 ^ 2) / 2 + s 0 * s 3 - s 1 * s 2
    - (1 - μ) / Real.sqrt ((s 0 + μ) ^ 2 + s 1 ^ 2)
    - μ / Real.sqrt ((s 0 - 1 + μ) ^ 2 + s 1 ^ 2)

def collisionFree (μ : ℝ) (s : Phase) : Prop :=
  0 < (s 0 + μ) ^ 2 + s 1 ^ 2 ∧
  0 < (s 0 - 1 + μ) ^ 2 + s 1 ^ 2

def coordinateVector (i : Fin 4) : Phase :=
  fun j => if j = i then 1 else 0

def partialDerivative (F : Phase → ℝ) (s : Phase) (i : Fin 4) : ℝ :=
  fderiv ℝ F s (coordinateVector i)

/-- The canonical Hamiltonian vector field `(∂H/∂p, -∂H/∂q)`. -/
def hamiltonianVectorField (F : Phase → ℝ) (s : Phase) : Phase :=
  ![partialDerivative F s 2, partialDerivative F s 3,
    -partialDerivative F s 0, -partialDerivative F s 1]

def isCriticalPoint (F : Phase → ℝ) (s : Phase) : Prop :=
  DifferentiableAt ℝ F s ∧ fderiv ℝ F s = 0

def criticalValueSet (μ : ℝ) : Set ℝ :=
  {e : ℝ | ∃ s : Phase,
    collisionFree μ s ∧ isCriticalPoint (jacobiHamiltonian μ) s ∧
      jacobiHamiltonian μ s = e}

/-- A collision-free equilibrium whose position lies strictly between the two
primaries on their common axis. -/
def IsInnerLagrangePoint (μ : ℝ) (s : Phase) : Prop :=
  collisionFree μ s ∧ isCriticalPoint (jacobiHamiltonian μ) s ∧
    -μ < s 0 ∧ s 0 < 1 - μ ∧ s 1 = 0

/-- The infimum of the collision-free critical values. For `0 < μ < 1`, the
identification theorem below is intended to show that this is `H(L₁)` in the
source's energy convention. -/
def firstCriticalValue (μ : ℝ) : ℝ :=
  sInf (criticalValueSet μ)

/-- The source writes a Jacobi energy level as `H = -c`; being below the first
critical value therefore means `-c < H(L₁)`. -/
def belowFirstCriticalValue (μ c : ℝ) : Prop :=
  -c < firstCriticalValue μ

/-- Squared distance to the second collision after the complex squaring map. -/
def secondCollisionDistanceSq (s : Phase) : ℝ :=
  (2 * (s 0 ^ 2 - s 1 ^ 2) - 1) ^ 2 + (4 * s 0 * s 1) ^ 2

/-- The totalized real-valued extension of Equation (2.2) of Joung--van Koert;
it agrees with the source formula where `secondCollisionDistanceSq s > 0`. -/
def leviCivitaHamiltonian (μ c : ℝ) (s : Phase) : ℝ :=
  wNormSq s / 2 + c * zNormSq s - (1 - μ) / 2
    + 2 * zNormSq s * (s 0 * s 3 - s 1 * s 2)
    - μ * (s 0 * s 3 + s 1 * s 2)
    - μ * zNormSq s / Real.sqrt (secondCollisionDistanceSq s)

/-- A canonical point over collision with the primary at `q=(-μ,0)`. -/
def leftCollisionPoint (μ : ℝ) : Phase :=
  ![0, 0, Real.sqrt (1 - μ), 0]

/-- The inverse position part of the Levi-Civita coordinate change
`q + μ = 2z²`. -/
def leviCivitaPosition (μ : ℝ) (s : Phase) : Plane :=
  ![2 * (s 0 ^ 2 - s 1 ^ 2) - μ, 4 * s 0 * s 1]

/-- The inverse momentum part of the Levi-Civita coordinate change
`p = w / conj z`, totalized at `z = 0`. -/
def leviCivitaMomentum (s : Phase) : Plane :=
  ![(s 2 * s 0 - s 3 * s 1) / zNormSq s,
    (s 2 * s 1 + s 3 * s 0) / zNormSq s]

/-- The collision-free inverse Levi-Civita coordinate map `(z,w) ↦ (q,p)`. -/
def leviCivitaToJacobi (μ : ℝ) (s : Phase) : Phase :=
  let q := leviCivitaPosition μ s
  let p := leviCivitaMomentum s
  ![q 0, q 1, p 0, p 1]

/-- The rotating-coordinate expression in Joung--van Koert, Proposition 2.2.
Strict positivity is their sufficient pointwise criterion for astronomical
retrograde motion with respect to the primary at `(-μ,0)`. -/
def retrogradeIndicator (μ : ℝ) (s : Phase) : ℝ :=
  let q := leviCivitaPosition μ s
  let p := leviCivitaMomentum s
  (q 0 + μ) * p 1 - q 1 * p 0 - μ * (q 0 + μ)

def regularEnergyLocus (μ c : ℝ) : Set Phase :=
  {s | leviCivitaHamiltonian μ c s = 0 ∧ 0 < secondCollisionDistanceSq s}

/-- The connected component based at the regularized collision over
`q=(-μ,0)`. Its intended physical interpretation uses `0 < μ < 1`. -/
def leftEnergyComponent (μ c : ℝ) : Set Phase :=
  connectedComponentIn (regularEnergyLocus μ c) (leftCollisionPoint μ)

abbrev LeftEnergyState (μ c : ℝ) := {s : Phase // s ∈ leftEnergyComponent μ c}

/-- A continuous flow on the left regularized energy component whose time derivative
is the Hamiltonian vector field of the Levi-Civita Hamiltonian. -/
def IsLeviCivitaHamiltonianFlow (μ c : ℝ)
    (φ : Flow ℝ (LeftEnergyState μ c)) : Prop :=
  ∀ s : LeftEnergyState μ c,
    HasDerivAt (fun t : ℝ => ((φ t s : LeftEnergyState μ c) : Phase))
      (hamiltonianVectorField (leviCivitaHamiltonian μ c) (s : Phase)) 0

/-- Compatibility of a flow with the antipodal deck transformation. This is
the condition needed for the flow to descend from the Levi-Civita cover to its
Moser-regularized quotient. -/
def IsAntipodallyEquivariantFlow (μ c : ℝ)
    (φ : Flow ℝ (LeftEnergyState μ c)) : Prop :=
  ∀ t : ℝ, ∀ s₁ s₂ : LeftEnergyState μ c,
    (s₂ : Phase) = -(s₁ : Phase) →
      ((φ t s₂ : LeftEnergyState μ c) : Phase) =
        -((φ t s₁ : LeftEnergyState μ c) : Phase)

structure PeriodicOrbit {X : Type*} [TopologicalSpace X]
    (φ : Flow ℝ X) where
  point : X
  period : ℝ
  period_pos : 0 < period
  closed : φ period point = point

def orbitSet {μ c : ℝ} {φ : Flow ℝ (LeftEnergyState μ c)}
    (γ : PeriodicOrbit φ) : Set Phase :=
  Set.range (fun t : ℝ => ((φ t γ.point : LeftEnergyState μ c) : Phase))

/-- The recorded period is a least positive period. -/
def IsSimplePeriodicOrbit {X : Type*} [TopologicalSpace X]
    (φ : Flow ℝ X) (γ : PeriodicOrbit φ) : Prop :=
  ∀ t : ℝ, 0 < t → t < γ.period → φ t γ.point ≠ γ.point

/-- The closed Levi-Civita orbit has least positive period and reaches the
antipodal point after half that period. For an antipodally equivariant flow on
a component with free antipodal action, this is the condition that its image
in the antipodal quotient is a prime orbit with a two-fold lifted iterate. -/
def IsAntipodalDoubleCover {μ c : ℝ}
    (φ : Flow ℝ (LeftEnergyState μ c)) (γ : PeriodicOrbit φ) : Prop :=
  IsSimplePeriodicOrbit φ γ ∧
    ((φ (γ.period / 2) γ.point : LeftEnergyState μ c) : Phase) =
      -(γ.point : Phase)

def relativePosition (μ : ℝ) (s : Phase) : Plane :=
  let q := leviCivitaPosition μ s
  ![q 0 + μ, q 1]

/-- A collision-free plane curve has the specified integer-style winding when
it admits a continuous polar lift whose angle changes by `2π * turns` over the
given period. -/
def HasPolarWinding (curve : ℝ → Plane) (period turns : ℝ) : Prop :=
  ∃ ρ θ : ℝ → ℝ,
    Continuous ρ ∧ Continuous θ ∧
    (∀ t : ℝ, 0 < ρ t) ∧
    (∀ t : ℝ,
      curve t = ![ρ t * Real.cos (θ t), ρ t * Real.sin (θ t)]) ∧
    (∀ t : ℝ, ρ (t + period) = ρ t) ∧
    (∀ t : ℝ, θ (t + period) = θ t + 2 * Real.pi * turns)

def jacobiQ₂Reflection (s : Phase) : Phase :=
  ![s 0, -s 1, -s 2, s 3]

/-- Data that represent a chosen lift of a prime noncontractible quotient
orbit when the component carries a free invariant antipodal cover and the flow
is equivariant. `period` is the intended quotient period: after that time the
chosen lift reaches its antipode, and no earlier positive time reaches either
candidate lift. -/
structure AntipodalPeriodicTrajectory {μ c : ℝ}
    (φ : Flow ℝ (LeftEnergyState μ c)) where
  point : LeftEnergyState μ c
  period : ℝ
  period_pos : 0 < period
  antipodal_closed :
    ((φ period point : LeftEnergyState μ c) : Phase) = -(point : Phase)
  prime : ∀ t : ℝ, 0 < t → t < period →
    ((φ t point : LeftEnergyState μ c) : Phase) ≠ (point : Phase) ∧
    ((φ t point : LeftEnergyState μ c) : Phase) ≠ -(point : Phase)

def IsQ₂SymmetricAntipodalTrajectory {μ c : ℝ}
    (φ : Flow ℝ (LeftEnergyState μ c))
    (δ : AntipodalPeriodicTrajectory φ) : Prop :=
  ∀ t : ℝ,
    leviCivitaToJacobi μ
        ((φ (-t) δ.point : LeftEnergyState μ c) : Phase) =
      jacobiQ₂Reflection
        (leviCivitaToJacobi μ
          ((φ t δ.point : LeftEnergyState μ c) : Phase))

/-- The geometric retrograde orbit in Birkhoff's shooting sense, represented
by one lifted period of its prime noncontractible quotient trajectory. Its
Jacobi position is a simple collision-free loop of winding `+1` around the
chosen primary and has the shooting construction's `q₂`-reflection symmetry.
The continuous polar lift permits temporary angular reversals, so this is
weaker than Joung--van Koert's pointwise astronomical inequality. -/
def IsGeometricBirkhoffRetrogradeTrajectory {μ c : ℝ}
    (φ : Flow ℝ (LeftEnergyState μ c))
    (δ : AntipodalPeriodicTrajectory φ) : Prop :=
    (∀ t : ℝ,
      0 < zNormSq ((φ t δ.point : LeftEnergyState μ c) : Phase)) ∧
    IsQ₂SymmetricAntipodalTrajectory φ δ ∧
    Set.InjOn
      (fun t : ℝ =>
        relativePosition μ ((φ t δ.point : LeftEnergyState μ c) : Phase))
      (Set.Ico 0 δ.period) ∧
    HasPolarWinding
      (fun t : ℝ =>
        relativePosition μ ((φ t δ.point : LeftEnergyState μ c) : Phase))
      δ.period 1

/-- The closed Levi-Civita double lift of an antipodally closed trajectory. -/
def antipodalTrajectoryDoubleLift {μ c : ℝ}
    (φ : Flow ℝ (LeftEnergyState μ c))
    (hanti : IsAntipodallyEquivariantFlow μ c φ)
    (δ : AntipodalPeriodicTrajectory φ) : PeriodicOrbit φ where
  point := δ.point
  period := 2 * δ.period
  period_pos := mul_pos (by norm_num) δ.period_pos
  closed := by
    apply Subtype.ext
    rw [show 2 * δ.period = δ.period + δ.period by ring,
      φ.map_add]
    calc
      ((φ δ.period (φ δ.period δ.point) : LeftEnergyState μ c) : Phase) =
          -((φ δ.period δ.point : LeftEnergyState μ c) : Phase) :=
        hanti δ.period δ.point (φ δ.period δ.point) δ.antipodal_closed
      _ = (δ.point : Phase) := by rw [δ.antipodal_closed]; simp

/-- A periodic orbit satisfying the strict pointwise inequality from
Joung--van Koert, Proposition 2.2. This is a sufficient condition for their
astronomical notion of retrograde motion and is stronger than Birkhoff's
shooting terminology (Remark 2.3). -/
def IsAstronomicallyRetrogradeOrbit {μ c : ℝ}
    (φ : Flow ℝ (LeftEnergyState μ c))
    (γ : PeriodicOrbit φ) : Prop :=
  ∀ t : ℝ,
    0 < zNormSq ((φ t γ.point : LeftEnergyState μ c) : Phase) ∧
    0 < retrogradeIndicator μ ((φ t γ.point : LeftEnergyState μ c) : Phase)

/-- A periodic orbit satisfying the strict pointwise direct-motion inequality
from Joung--van Koert, Proposition 2.2. -/
def IsAstronomicallyDirectOrbit {μ c : ℝ}
    (φ : Flow ℝ (LeftEnergyState μ c))
    (γ : PeriodicOrbit φ) : Prop :=
  ∀ t : ℝ,
    0 < zNormSq ((φ t γ.point : LeftEnergyState μ c) : Phase) ∧
    retrogradeIndicator μ ((φ t γ.point : LeftEnergyState μ c) : Phase) < 0

def planeNormSq (u : Plane) : ℝ := u 0 ^ 2 + u 1 ^ 2

def closedUnitDisk : Set Plane := {u | planeNormSq u ≤ 1}

def openUnitDisk : Set Plane := {u | planeNormSq u < 1}

def unitCircle : Set Plane := {u | planeNormSq u = 1}

/-- The round unit three-sphere in the four real phase coordinates. -/
def unitThreeSphere : Set Phase :=
  {s | zNormSq s + wNormSq s = 1}

/-- A homeomorphism from the selected component to the round three-sphere that
intertwines their antipodal maps. -/
def IsAntipodallyEquivariantSphereHomeomorph {μ c : ℝ}
    (e : LeftEnergyState μ c ≃ₜ {x : Phase // x ∈ unitThreeSphere}) : Prop :=
  ∀ s₁ s₂ : LeftEnergyState μ c,
    (s₂ : Phase) = -(s₁ : Phase) →
      ((e s₂ : {x : Phase // x ∈ unitThreeSphere}) : Phase) =
        -((e s₁ : {x : Phase // x ∈ unitThreeSphere}) : Phase)

/-- A smooth embedded disk whose boundary is a periodic orbit, whose interior is
transverse to the Hamiltonian flow, and which every other trajectory meets at
arbitrarily large positive and negative times. -/
def DiskLikeGlobalSurfaceOfSection {μ c : ℝ}
    (φ : Flow ℝ (LeftEnergyState μ c)) (γ : PeriodicOrbit φ) : Prop :=
  ∃ page : Plane → Phase,
    (∀ u ∈ closedUnitDisk, ContDiffAt ℝ ∞ page u) ∧
    (∀ u ∈ closedUnitDisk, page u ∈ leftEnergyComponent μ c) ∧
    Set.InjOn page closedUnitDisk ∧
    (∀ u ∈ closedUnitDisk, Function.Injective (fderiv ℝ page u)) ∧
    (∀ u ∈ openUnitDisk,
      hamiltonianVectorField (leviCivitaHamiltonian μ c) (page u) ∉
        Set.range (fderiv ℝ page u)) ∧
    page '' unitCircle = orbitSet γ ∧
    (∀ s : LeftEnergyState μ c, (s : Phase) ∉ orbitSet γ →
      (∀ R : ℝ, ∃ t : ℝ, R < t ∧
        ((φ t s : LeftEnergyState μ c) : Phase) ∈ page '' openUnitDisk) ∧
      (∀ R : ℝ, ∃ t : ℝ, t < R ∧
        ((φ t s : LeftEnergyState μ c) : Phase) ∈ page '' openUnitDisk))

/-- The relation that identifies equal or antipodal states of the selected
Levi-Civita component. In the physical subcritical regime, this is the deck
relation for the cover in Joung--van Koert, Proposition 2.4. -/
def antipodalEquivalent {μ c : ℝ}
    (x y : LeftEnergyState μ c) : Prop :=
  (x : Phase) = (y : Phase) ∨ (x : Phase) = -(y : Phase)

/-- The selected component is preserved by the antipodal deck map. -/
def IsAntipodallyInvariantComponent (μ c : ℝ) : Prop :=
  ∀ s : Phase,
    s ∈ leftEnergyComponent μ c ↔ -s ∈ leftEnergyComponent μ c

/-- The antipodal deck map has no fixed point on the selected component. -/
def IsAntipodallyFreeComponent (μ c : ℝ) : Prop :=
  ∀ s : LeftEnergyState μ c, (s : Phase) ≠ -(s : Phase)

/-- The equivalence relation generated by the antipodal deck transformation. -/
def antipodalSetoid (μ c : ℝ) : Setoid (LeftEnergyState μ c) where
  r := antipodalEquivalent
  iseqv := by
    constructor
    · intro x
      exact Or.inl rfl
    · intro x y h
      rcases h with h | h
      · exact Or.inl h.symm
      · exact Or.inr (by
          simpa using (congrArg (fun s : Phase => -s) h).symm)
    · intro x y z hxy hyz
      rcases hxy with hxy | hxy <;> rcases hyz with hyz | hyz
      · exact Or.inl (hxy.trans hyz)
      · exact Or.inr (hxy.trans hyz)
      · exact Or.inr (hxy.trans (congrArg (fun s : Phase => -s) hyz))
      · exact Or.inl (hxy.trans (by
          simpa using congrArg (fun s : Phase => -s) hyz))

/-- The selected regularized component modulo the antipodal deck map. Proposition
2.4 of Joung--van Koert identifies this quotient with the relevant Moser
regularized `ℝP³` component in the physical subcritical regime. -/
abbrev AntipodalQuotientState (μ c : ℝ) :=
  Quotient (antipodalSetoid μ c)

def toAntipodalQuotient {μ c : ℝ}
    (s : LeftEnergyState μ c) : AntipodalQuotientState μ c :=
  Quotient.mk (antipodalSetoid μ c) s

/-- The time-`t` map descended to the antipodal quotient. The equivariance
hypothesis makes the result independent of the chosen lift. -/
def quotientTimeMap {μ c : ℝ}
    (φ : Flow ℝ (LeftEnergyState μ c))
    (hanti : IsAntipodallyEquivariantFlow μ c φ) (t : ℝ) :
    AntipodalQuotientState μ c → AntipodalQuotientState μ c :=
  Quotient.map (fun s => φ t s) (by
    intro x y hxy
    rcases hxy with hxy | hxy
    · have h : x = y := Subtype.ext hxy
      subst y
      exact Or.inl rfl
    · exact Or.inr (hanti t y x hxy))

/-- The descended time maps are jointly continuous and satisfy the identity
and composition laws of a real flow. -/
def IsContinuousQuotientDynamics {μ c : ℝ}
    (φ : Flow ℝ (LeftEnergyState μ c))
    (hanti : IsAntipodallyEquivariantFlow μ c φ) : Prop :=
  Continuous (Function.uncurry (quotientTimeMap φ hanti)) ∧
  (∀ x : AntipodalQuotientState μ c,
    quotientTimeMap φ hanti 0 x = x) ∧
  ∀ t₁ t₂ : ℝ, ∀ x : AntipodalQuotientState μ c,
    quotientTimeMap φ hanti (t₁ + t₂) x =
      quotientTimeMap φ hanti t₁ (quotientTimeMap φ hanti t₂ x)

def quotientOrbitSet {μ c : ℝ}
    {φ : Flow ℝ (LeftEnergyState μ c)}
    (hanti : IsAntipodallyEquivariantFlow μ c φ)
    (γ : PeriodicOrbit φ) : Set (AntipodalQuotientState μ c) :=
  Set.range (fun t : ℝ =>
    quotientTimeMap φ hanti t (toAntipodalQuotient γ.point))

/-- The half-period image of the lifted orbit is a prime periodic orbit in the
antipodal quotient. -/
def IsPrimeQuotientBinding {μ c : ℝ}
    (φ : Flow ℝ (LeftEnergyState μ c))
    (hanti : IsAntipodallyEquivariantFlow μ c φ)
    (γ : PeriodicOrbit φ) : Prop :=
  quotientTimeMap φ hanti (γ.period / 2)
      (toAntipodalQuotient γ.point) = toAntipodalQuotient γ.point ∧
    ∀ t : ℝ, 0 < t → t < γ.period / 2 →
      quotientTimeMap φ hanti t (toAntipodalQuotient γ.point) ≠
        toAntipodalQuotient γ.point

abbrev ClosedDiskPoint := {u : Plane // u ∈ closedUnitDisk}

def closedDiskInterior : Set ClosedDiskPoint :=
  {u | (u : Plane) ∈ openUnitDisk}

def closedDiskBoundary : Set ClosedDiskPoint :=
  {u | (u : Plane) ∈ unitCircle}

abbrev ClosedDiskInteriorPoint :=
  {u : ClosedDiskPoint // u ∈ closedDiskInterior}

/-- The quotient page induced by a chosen smooth lift on the closed disk. -/
def quotientDiskPage {μ c : ℝ} (page : Plane → Phase)
    (hpage : ∀ u ∈ closedUnitDisk, page u ∈ leftEnergyComponent μ c) :
    ClosedDiskPoint → AntipodalQuotientState μ c :=
  fun u => toAntipodalQuotient
    ⟨page (u : Plane), hpage (u : Plane) u.property⟩

def quotientDiskInteriorPage {μ c : ℝ} (page : Plane → Phase)
    (hpage : ∀ u ∈ closedUnitDisk, page u ∈ leftEnergyComponent μ c) :
    ClosedDiskInteriorPoint → AntipodalQuotientState μ c :=
  fun u => quotientDiskPage page hpage u.1

/-- A cover-lift encoding of a rational two-disk global surface of section in
the topological antipodal quotient. The lifted disk is smooth
and immersive, its quotient interior is embedded and disjoint from the binding,
and antipodal boundary parameters are exactly the fibers of the two-fold
boundary map. Transversality is checked on the lift. Arbitrarily far positive
and negative returns are stated for the well-defined descended time maps. -/
def RationalDiskLikeGlobalSurfaceOfSection {μ c : ℝ}
    (φ : Flow ℝ (LeftEnergyState μ c))
    (hanti : IsAntipodallyEquivariantFlow μ c φ)
    (γ : PeriodicOrbit φ) : Prop :=
  IsAntipodallyInvariantComponent μ c ∧
  IsAntipodallyFreeComponent μ c ∧
  IsContinuousQuotientDynamics φ hanti ∧
  IsPrimeQuotientBinding φ hanti γ ∧
  ∃ (page : Plane → Phase)
      (hpage : ∀ u ∈ closedUnitDisk,
        page u ∈ leftEnergyComponent μ c),
    (∀ u ∈ closedUnitDisk, ContDiffAt ℝ ∞ page u) ∧
    Set.InjOn page closedUnitDisk ∧
    (∀ u ∈ closedUnitDisk, Function.Injective (fderiv ℝ page u)) ∧
    (∀ u ∈ openUnitDisk,
      hamiltonianVectorField (leviCivitaHamiltonian μ c) (page u) ∉
        Set.range (fderiv ℝ page u)) ∧
    page '' unitCircle = orbitSet γ ∧
    Continuous (quotientDiskPage page hpage) ∧
    Topology.IsEmbedding (quotientDiskInteriorPage page hpage) ∧
    (∀ u v : ClosedDiskPoint,
      (quotientDiskPage page hpage u = quotientDiskPage page hpage v ↔
        (u : Plane) = (v : Plane) ∨
          (u ∈ closedDiskBoundary ∧ v ∈ closedDiskBoundary ∧
            (v : Plane) = -(u : Plane)))) ∧
    quotientDiskPage page hpage '' closedDiskBoundary =
      quotientOrbitSet hanti γ ∧
    (∀ x : AntipodalQuotientState μ c,
      x ∉ quotientOrbitSet hanti γ →
      (∀ R : ℝ, ∃ t : ℝ, R < t ∧
        quotientTimeMap φ hanti t x ∈
          quotientDiskPage page hpage '' closedDiskInterior) ∧
      (∀ R : ℝ, ∃ t : ℝ, t < R ∧
        quotientTimeMap φ hanti t x ∈
          quotientDiskPage page hpage '' closedDiskInterior))

/-- Twice differentiability and positive tangential Hessian on a subset. This is
the differential condition used in the convexity calculation; it does not by
itself assert that the subset bounds a convex body. -/
def HasPositiveTangentialHessianOn (F : Phase → ℝ) (S : Set Phase) : Prop :=
  (∀ s ∈ S, ContDiffAt ℝ 2 F s) ∧
  ∀ s ∈ S, ∀ v : Phase, v ≠ 0 → fderiv ℝ F s v = 0 →
    0 < fderiv ℝ (fun x => fderiv ℝ F x v) s v

end

end BirkhoffGlobalSection
