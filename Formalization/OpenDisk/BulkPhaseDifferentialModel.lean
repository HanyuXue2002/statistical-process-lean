import Formalization.OpenDisk.BulkPhaseGraph
import Formalization.OpenDisk.ConePhaseCapConverse

/-! The completion interface constructed from a genuine previous differential
`D : U → closed(B)`, an arbitrary actual closed-cochain subgroup, and the
explicit closed restriction surjectivity. The canonical primitive is proved
to be exactly the cap formula used in the intrinsic-locality equivalence. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

namespace OpenDisk.BulkPhaseDifferentialModel

open GeneralSphereT.PathAlgebra
open BulkPhase BulkPhaseCompletion BulkPhaseGraph ConePhaseLocalLift

variable {I ι κ G A P : Type*} [AddCommGroup I] [LinearOrder ι] [LinearOrder κ]
  [AddCommGroup G] [AddCommGroup A] [AddCommGroup P]
variable (d : Configuration ι G →+ A) (D : Configuration κ G →+ d.ker)
  (hD : Function.Surjective D)
  (H : AddSubgroup (I × Configuration ι G))
  (hclosed : ∀ a : H, a.val.2 ∈ d.ker)
  (hext : ∀ z : d.ker, ∃ a : H, a.val.2 = z.val)

def differentialModel : Model I (Configuration κ G) (Configuration ι G) where
  actualClosed := H
  capClosed := (capDifferential (d.ker.subtype.comp D)).ker
  boundaryClosed := d.ker
  actual_closed := hclosed
  cap_closed := by
    intro c
    have hc : c.val.2 = (D c.val.1 : Configuration ι G) := (closedCap_iff _ _).1 c.property
    rw [hc]
    exact (D c.val.1).property
  actual_extension := hext
  cap_extension := by
    intro z
    obtain ⟨w, hw⟩ := hD z
    refine ⟨⟨(w, z.val), (closedCap_iff _ _).2 ?_⟩, rfl⟩
    exact (congrArg Subtype.val hw).symm
  splitting := capSplitting (d.ker.subtype.comp D)
  base_new_zero := fun _ => rfl
  base_zero_slice := by intro b; simp

local notation "M" => differentialModel d D hD H hclosed hext

theorem canonicalCap_formula (F : d.ker → Configuration ι G → P)
    (u : Configuration κ G) (b : Configuration ι G) :
    canonicalCap (M).capSystem (M).splitting F (u, b) =
      F (D u) (b - (D u : Configuration ι G)) := by
  have hz : (M).capSystem.closedRestriction ((M).splitting.closedPart (u, b)) = D u := by
    apply Subtype.ext
    change b - (b - (D u : Configuration ι G)) = (D u : Configuration ι G)
    abel
  change F ((M).capSystem.closedRestriction ((M).splitting.closedPart (u, b)))
    (b - (D u : Configuration ι G)) = _
  rw [hz]

/-- The previously constructed completion cap is the literal local-lift cap
after the standard cochain sum/product identification. -/
theorem canonicalCap_eq_capPhase (F : SymmetryPhase d P)
    (c : Configuration (κ ⊕ ι) G) :
    canonicalCap (M).capSystem (M).splitting F (capParts c) = capPhase d D F c := by
  rw [canonicalCap_formula]
  rfl

def bulkSymmetry (t : BulkDatum M P) : SymmetryPhase d P :=
  ⟨t.val.2, bulkDatum_isCocycle M t⟩

theorem complete_capSlice (t : BulkDatum M P) :
    capSlice (complete M t).val = canonicalCap (M).capSystem (M).splitting t.val.2 := by
  have h := capSlice_eq_canonical M (complete M t).property.1 (complete M t).property.2
  have hr : recoveredResponse M (complete M t).val = t.val.2 :=
    congrArg (fun x : BulkDatum M P => x.val.2) (recover_complete M t)
  rw [hr] at h
  exact h

end OpenDisk.BulkPhaseDifferentialModel
