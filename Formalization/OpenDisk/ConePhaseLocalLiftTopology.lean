import Formalization.OpenDisk.ConePhaseLocalLift

/-! The explicit local lift is additive and continuous in the full symmetry
table. The cochain contraction is fixed before the symmetry table is chosen. -/

noncomputable section
set_option linter.unusedSectionVars false

namespace OpenDisk.ConePhaseLocalLift

open GeneralSphereT.PathAlgebra

variable {ι κ G A P : Type*} [LinearOrder ι] [LinearOrder κ]
  [AddCommGroup G] [AddCommGroup A] [AddCommGroup P]
variable (d : Configuration ι G →+ A) (D : Configuration κ G →+ d.ker)
  (h : Configuration ι G →+ Configuration κ G) (i : ι) (g : G)

/-- The fixed-contraction lift as an additive map of full phase tables. -/
def localLiftHom : SymmetryPhase d P →+ (Configuration ι G → P) where
  toFun F := localLift d D F h i g
  map_zero' := by
    funext v
    change (0 : P) - 0 = 0
    simp
  map_add' F H := by
    funext v
    change localLift d D (F + H) h i g v =
      localLift d D F h i g v + localLift d D H h i g v
    simp only [localLift, phaseDifference, capPhase, AddSubgroup.coe_add, Pi.add_apply]
    abel

@[simp] theorem localLiftHom_apply (F : SymmetryPhase d P) (v : Configuration ι G) :
    localLiftHom d D h i g F v = localLift d D F h i g v := rfl

theorem continuous_localLiftHom [TopologicalSpace P] [IsTopologicalAddGroup P] :
    Continuous (localLiftHom (P := P) d D h i g) := by
  apply continuous_pi
  intro v
  have hev (z : d.ker) (c : Configuration ι G) :
      Continuous (fun F : SymmetryPhase d P => F z c) :=
    (continuous_apply c).comp ((continuous_apply z).comp continuous_subtype_val)
  exact (hev _ _).sub (hev _ _)

end OpenDisk.ConePhaseLocalLift
