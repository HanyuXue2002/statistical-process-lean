import Formalization.OpenDisk.StarMarkedPhases
import Formalization.OpenDisk.JointLocality

set_option linter.style.header false

/-!
# Path connectedness of the actual symmetry kernel

The nontrivial input is the geometric curvature decomposition proved in
`StarMarkedPhases`. Every closed marked row is a continuous image of a full
product of coefficient groups. Taking all elementary rows and all physical
configuration-basis phases proves the actual symmetry kernel path connected.
-/

noncomputable section

open scoped BigOperators
open GeneralSphereT.PathAlgebra GeneralSphereT.SimplicialCochain

namespace OpenDisk.StarLocality

variable {V G P : Type*} [LinearOrder V] [Fintype V]
  [AddCommGroup G] [AddCommGroup P] [TopologicalSpace P] [IsTopologicalAddGroup P]

variable (K : AbstractSimplicialComplex V) (n : ℕ)

local instance topologyFaceOrder : LinearOrder (Simplex K n) := by
  classical
  exact linearOrderOfSTO WellOrderingRel

local instance topologySimplexFintype : Fintype (NonemptySimplex K) := Fintype.ofFinite _

abbrev ClosedMarkedRow (η : Simplex K n) :=
  (localFunctionSubgroup (G := G) (markedFacets (simplicialFacets K n) {η}) P ⊓
    (phaseDerivative (coboundaryToRange (G := G) K n) (P := P)).ker :
      AddSubgroup (Cochain K n G → P))

theorem continuous_globalMarkedCurvatureSum (η : Simplex K n) :
    Continuous (globalMarkedCurvatureSum (G := G) (P := P) K n η) := by
  apply continuous_pi
  intro c
  unfold globalMarkedCurvatureSum
  fun_prop

/-- Each actual closed marked row is path connected, by its proved
simplex-curvature parametrization, including its constant phase. -/
theorem closedMarkedRow_pathConnectedSpace [PathConnectedSpace P] (η : Simplex K n) :
    PathConnectedSpace (ClosedMarkedRow (G := G) (P := P) K n η) := by
  let lift : (∀ ρ : CarrierFacets K n η, Configuration (facesIn K (n + 1) ρ.val) G → P) →
      ClosedMarkedRow (G := G) (P := P) K n η := fun k =>
    ⟨globalMarkedCurvatureSum K n η k, globalMarkedCurvatureSum_marked K n η k,
      globalMarkedCurvatureSum_closed K n η k⟩
  have hcont : Continuous lift := (continuous_globalMarkedCurvatureSum K n η).subtype_mk _
  have hsurj : Function.Surjective lift := by
    intro f
    obtain ⟨k, hk⟩ := exists_globalMarkedCurvatureSum K n η f.val f.property.1 f.property.2
    exact ⟨k, Subtype.ext hk.symm⟩
  exact hsurj.pathConnectedSpace hcont

/-- Separate all elementary hopping labels into their literal closed marked rows. -/
def closedMarkedHoppingsHomeomorph :
    closedMarkedHoppings (coboundaryToRange (G := G) K n)
      (markedFunctionSubgroup (P := P) (simplicialFacets K n)) ≃ₜ
      (∀ e : ElementaryLabel (Simplex K n) G, ClosedMarkedRow (G := G) (P := P) K n e.val.1) where
  toFun L e := ⟨L.val e, L.property.1 e, L.property.2 e⟩
  invFun f := ⟨fun e => (f e).val, fun e => (f e).property.1, fun e => (f e).property.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := by
    apply continuous_pi
    intro e
    exact ((continuous_apply e).comp continuous_subtype_val).subtype_mk _
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact continuous_pi fun e => continuous_subtype_val.comp (continuous_apply e)

/-- All closed marked hopping tables on an actual simplicial complex are path connected. -/
theorem closedMarkedHoppings_pathConnectedSpace [PathConnectedSpace P] :
    PathConnectedSpace (closedMarkedHoppings (coboundaryToRange (G := G) K n)
      (markedFunctionSubgroup (P := P) (simplicialFacets K n))) := by
  letI (e : ElementaryLabel (Simplex K n) G) :
      PathConnectedSpace (ClosedMarkedRow (G := G) (P := P) K n e.val.1) :=
    closedMarkedRow_pathConnectedSpace K n e.val.1
  exact (closedMarkedHoppingsHomeomorph (G := G) (P := P) K n).symm.pathConnectedSpace

/-- The actual symmetry forgetful kernel in (5.5) is path connected.
No connectedness or local lifting premise is introduced. -/
theorem simplicial_symmetryKernel_pathConnectedSpace [PathConnectedSpace P]
    (rep : CoboundaryGroup (G := G) K n → Cochain K n G)
    (hrep : ∀ a, coboundaryToRange K n (rep a) = a) :
    PathConnectedSpace
      (forgetSymmetry (coboundaryToRange (G := G) K n) elementaryStep
        (markedFunctionSubgroup (P := P) (simplicialFacets K n))).ker := by
  letI := closedMarkedHoppings_pathConnectedSpace (G := G) (P := P) K n
  exact (symmetryKernelHomeomorph (coboundaryToRange (G := G) K n) elementaryStep
    (markedFunctionSubgroup (P := P) (simplicialFacets K n)) rep hrep).symm.pathConnectedSpace

end OpenDisk.StarLocality
