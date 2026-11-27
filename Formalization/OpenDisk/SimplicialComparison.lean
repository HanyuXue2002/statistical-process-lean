import Formalization.OpenDisk.ConePhaseSimplicialLocalLiftSection
import Formalization.OpenDisk.StarMarkedTopology
import Formalization.OpenDisk.ComponentClassification

/-!
# Both forgetful maps on actual finite ordered simplicial cochains

The symmetry section uses the proved star contraction lift, including degree
zero. Both kernels are proved path connected. Consequently anomaly and
excitation components are canonically isomorphic abelian groups on the same
literal simplicial model, without a sphere or classification assumption.
-/

noncomputable section
set_option maxHeartbeats 1000000

namespace OpenDisk.SimplicialComparison
open GeneralSphereT.SimplicialCochain GeneralSphereT.PathAlgebra
open ConePhaseSimplicialLocalLift StarLocality

variable {V G P : Type*} [LinearOrder V] [Fintype V]
  [AddCommGroup G] [AddCommGroup P]
  (K : AbstractSimplicialComplex V) (n : ℕ)

local instance comparisonOrder : LinearOrder (Simplex K n) := by
  classical
  exact linearOrderOfSTO WellOrderingRel

def representative (a : CoboundaryGroup (G := G) K n) : Cochain K n G :=
  Classical.choose (coboundaryToRange_surjective K n a)

theorem representative_spec (a : CoboundaryGroup (G := G) K n) :
    coboundaryToRange K n (representative K n a) = a :=
  Classical.choose_spec (coboundaryToRange_surjective K n a)

abbrev JointSpace := LocalJointPhase (simplicialFacets K n) (coboundaryToRange (G := G) K n) P
abbrev SymmetrySpace := localSymmetries (simplicialFacets K n) (coboundaryToRange (G := G) K n) (P := P)
abbrev ExcitationSpace := ExcitationPhase (simplicialFacets K n) (coboundaryToRange (G := G) K n) P

def symmetryProjection : JointSpace (P := P) K n →+ SymmetrySpace (P := P) K n where
  toFun x := ⟨forgetSymmetry _ _ _ x, joint_forgetSymmetry_local _ _ x⟩
  map_zero' := Subtype.ext (map_zero _)
  map_add' x y := Subtype.ext (map_add _ x y)

/-- No existence choice varies with F: both components are fixed additive formulas. -/
def symmetrySection : SymmetrySpace (P := P) K n →+ JointSpace (P := P) K n where
  toFun F := ⟨(phaseSection (coboundaryToRange K n) (representative K n)
      (representative_spec K n) F.val, simplicialHoppingLiftHom K n F.val),
    simplicialHoppingLift_marked K n F.val F.property, by
      intro e z v
      change difference (simplicialHoppingLiftHom K n F.val e) z v =
        difference (fun w => phaseDerivative (coboundaryToRange K n)
          (phaseSection (coboundaryToRange K n) (representative K n)
            (representative_spec K n) F.val) z w) (elementaryStep e) v
      rw [phaseDerivative_phaseSection]
      exact simplicialHoppingLift_matches K n F.val F.property e z v⟩
  map_zero' := by
    apply Subtype.ext
    exact Prod.ext (map_zero _) (map_zero _)
  map_add' F H := by
    apply Subtype.ext
    exact Prod.ext (map_add _ F.val H.val) (map_add _ F.val H.val)

theorem symmetryProjection_section (F : SymmetrySpace (P := P) K n) :
    symmetryProjection K n (symmetrySection K n F) = F :=
  Subtype.ext (phaseDerivative_phaseSection _ _ _ F.val)

theorem symmetryProjection_surjective : Function.Surjective (symmetryProjection (P := P) K n) :=
  Function.RightInverse.surjective (symmetryProjection_section K n)

section Topology
variable [TopologicalSpace P] [IsTopologicalAddGroup P]

theorem continuous_symmetryProjection : Continuous (symmetryProjection (P := P) K n) :=
  (continuous_forgetSymmetry _ _ _).subtype_mk _

theorem continuous_symmetrySection : Continuous (symmetrySection (P := P) K n) :=
  (((continuous_phaseSection _ _ _).comp continuous_subtype_val).prodMk
    ((continuous_simplicialHoppingLiftHom K n).comp continuous_subtype_val)).subtype_mk _

def symmetryProjectionKernelHomeomorph : (symmetryProjection (P := P) K n).ker ≃ₜ
    (forgetSymmetry (coboundaryToRange (G := G) K n) elementaryStep
      (markedFunctionSubgroup (P := P) (simplicialFacets K n))).ker := by
  have heq : (symmetryProjection (P := P) K n).ker =
      (forgetSymmetry (coboundaryToRange (G := G) K n) elementaryStep
        (markedFunctionSubgroup (P := P) (simplicialFacets K n))).ker := by
    ext x
    constructor
    · intro hx; exact congrArg Subtype.val hx
    · intro hx; exact Subtype.ext hx
  exact Homeomorph.setCongr (congrArg SetLike.coe heq)

theorem symmetryProjectionKernel_pathConnectedSpace [PathConnectedSpace P] :
    PathConnectedSpace (symmetryProjection (P := P) K n).ker := by
  letI := simplicial_symmetryKernel_pathConnectedSpace (G := G) (P := P) K n
    (representative K n) (representative_spec K n)
  exact (symmetryProjectionKernelHomeomorph (G := G) (P := P) K n).symm.pathConnectedSpace

def jointSymmetryProductHomeomorph : JointSpace (P := P) K n ≃ₜ
    SymmetrySpace (P := P) K n × (symmetryProjection (P := P) K n).ker :=
  (splitContinuousAddEquiv (symmetryProjection K n) (symmetrySection K n)
    (symmetryProjection_section K n) (continuous_symmetryProjection K n)
    (continuous_symmetrySection K n)).toHomeomorph

def jointSymmetryQuotientHomeomorph :
    (JointSpace (P := P) K n ⧸ (symmetryProjection (P := P) K n).ker) ≃ₜ
      SymmetrySpace (P := P) K n :=
  splitQuotientHomeomorph (X := JointSpace (P := P) K n) (Y := SymmetrySpace (P := P) K n)
    (symmetryProjection K n) (symmetrySection K n) (symmetryProjection_section K n)
    (continuous_symmetryProjection K n) (continuous_symmetrySection K n)

def jointSymmetryComponentEquiv [PathConnectedSpace P] :
    ComponentGroup (JointSpace (P := P) K n) ≃+ ComponentGroup (SymmetrySpace (P := P) K n) := by
  letI := symmetryProjectionKernel_pathConnectedSpace (G := G) (P := P) K n
  exact splitComponentGroupEquiv (symmetryProjection K n) (symmetrySection K n)
    (symmetryProjection_section K n) (continuous_symmetryProjection K n)
    (continuous_symmetrySection K n)

end Topology

variable [Nonempty (NonemptySimplex K)]

/-- Corollary 5.4 before the final sphere-cohomology computation. -/
def anomalyStatisticsComponentEquiv :
    ComponentGroup (SymmetrySpace (G := G) (P := AddCircle (1 : ℝ)) K n) ≃+
      ComponentGroup (ExcitationSpace (G := G) (P := AddCircle (1 : ℝ)) K n) :=
  (jointSymmetryComponentEquiv (G := G) (P := AddCircle (1 : ℝ)) K n).symm.trans
    (jointExcitationComponentGroupEquiv (simplicialFacets K n) (coboundaryToRange K n)
      (representative K n) (representative_spec K n) (simplex_mem_some_facesIn K n))

end OpenDisk.SimplicialComparison
