import Formalization.OpenDisk.BulkPhaseDifferentialModel
import Formalization.OpenDisk.SymmetryComponentSpace

/-!
# Canonical completion on the literal local phase-table subgroups

The bulk side consists of an actual local phase and an intrinsically local
boundary response satisfying the bulk response equation. The completed side
consists of closed-invariant separated tables whose normalized actual and cap
slices have their literal coordinate locality. The cap converse and the
explicit previous differential prove that the full-table completion restricts
to a continuous additive equivalence of these groups.

`BulkPhaseSimplicialGluing` identifies the two slice-locality conditions with
ordinary simplex locality after adjoining the actual new cone vertex.
Closed extension and boundary cochain exactness remain explicit cochain data.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000

namespace OpenDisk.BulkPhaseDifferentialModel

open GeneralSphereT.PathAlgebra
open BulkPhase BulkPhaseCompletion ConePhaseLocalLift

variable {I ι κ G A P Facet : Type*} [AddCommGroup I] [LinearOrder ι] [LinearOrder κ]
  [AddCommGroup G] [AddCommGroup A] [AddCommGroup P]
variable (d : Configuration ι G →+ A) (D : Configuration κ G →+ d.ker)
  (hD : Function.Surjective D)
  (H : AddSubgroup (I × Configuration ι G))
  (hclosed : ∀ a : H, a.val.2 ∈ d.ker)
  (hext : ∀ z : d.ker, ∃ a : H, a.val.2 = z.val)

local instance sumOrderLocalCompletion : LinearOrder (κ ⊕ ι) :=
  inferInstanceAs (LinearOrder (κ ⊕ₗ ι))

local notation "M" => differentialModel d D hD H hclosed hext

def bulkPhaseHom : BulkDatum M P →+ (I × Configuration ι G → P) where
  toFun t := t.val.1
  map_zero' := rfl
  map_add' _ _ := rfl

def bulkResponseHom : BulkDatum M P →+ SymmetryPhase d P where
  toFun t := bulkSymmetry d D hD H hclosed hext t
  map_zero' := rfl
  map_add' _ _ := rfl

def completionActualSliceHom : CompletedDatum M P →+ (I × Configuration ι G → P) where
  toFun Ψ := actualSlice Ψ.val
  map_zero' := rfl
  map_add' _ _ := rfl

def completionCapSliceHom : CompletedDatum M P →+ (Configuration (κ ⊕ ι) G → P) where
  toFun Ψ c := capSlice Ψ.val (capParts c)
  map_zero' := by funext c; exact sub_zero (0 : P)
  map_add' Ψ Ω := by
    funext c
    change (Ψ.val 0 (boundaryPart c) (newPart c) + Ω.val 0 (boundaryPart c) (newPart c)) -
      (Ψ.val 0 (boundaryPart c) 0 + Ω.val 0 (boundaryPart c) 0) =
      (Ψ.val 0 (boundaryPart c) (newPart c) - Ψ.val 0 (boundaryPart c) 0) +
      (Ω.val 0 (boundaryPart c) (newPart c) - Ω.val 0 (boundaryPart c) 0)
    abel

variable (actualLocal : AddSubgroup (I × Configuration ι G → P))
  (facets : Facet → Set ι) (newFacets : Facet → Set κ)

def localBulkSubgroup : AddSubgroup (BulkDatum M P) :=
  actualLocal.comap (bulkPhaseHom d D hD H hclosed hext) ⊓
    (localSymmetries facets d).comap (bulkResponseHom d D hD H hclosed hext)

def localCompletedSubgroup : AddSubgroup (CompletedDatum M P) :=
  actualLocal.comap (completionActualSliceHom d D hD H hclosed hext) ⊓
    (localFunctionSubgroup (capFacets facets newFacets) P).comap
      (completionCapSliceHom d D hD H hclosed hext)

variable (hcover : ∀ i, ∃ ρ, i ∈ facets ρ)
  (hcolumns : ∀ ρ k, k ∉ newFacets ρ → ∀ g,
    coordinateRestriction (facets ρ) (D (Finsupp.single k g) : Configuration ι G) = 0)
  (hrelative : RelativeCapLifts d facets newFacets D)

theorem complete_mem_local_iff (t : BulkDatum M P) :
    complete M t ∈ localCompletedSubgroup d D hD H hclosed hext actualLocal facets newFacets ↔
      t ∈ localBulkSubgroup d D hD H hclosed hext actualLocal facets := by
  change (actualSlice (complete M t).val ∈ actualLocal ∧
    AnchoredLocal (capFacets facets newFacets)
      (fun c => capSlice (complete M t).val (capParts c))) ↔
    (t.val.1 ∈ actualLocal ∧ RestrictionSymmetryLocal facets d (bulkSymmetry d D hD H hclosed hext t))
  have ha : actualSlice (complete M t).val = t.val.1 := recover_complete_phase M t
  have hc : (fun c => capSlice (complete M t).val (capParts c)) =
      capPhase d D (bulkSymmetry d D hD H hclosed hext t) := by
    funext c
    rw [complete_capSlice]
    exact canonicalCap_eq_capPhase d D hD H hclosed hext
      (bulkSymmetry d D hD H hclosed hext t) c
  rw [ha, hc, ← differenceLocal_iff_anchoredLocal]
  exact and_congr_right fun _ => capPhase_local_iff d facets newFacets hcover D hcolumns
    hrelative (bulkSymmetry d D hD H hclosed hext t)

/-- The local version of the full canonical completion equivalence. -/
def localCompletionAddEquiv :
    localBulkSubgroup d D hD H hclosed hext actualLocal facets ≃+
      localCompletedSubgroup d D hD H hclosed hext actualLocal facets newFacets where
  toFun t := ⟨complete M t.val,
    (complete_mem_local_iff d D hD H hclosed hext actualLocal facets newFacets
      hcover hcolumns hrelative t.val).2 t.property⟩
  invFun Ψ := ⟨recover M Ψ.val,
    (complete_mem_local_iff d D hD H hclosed hext actualLocal facets newFacets
      hcover hcolumns hrelative (recover M Ψ.val)).1 (by
        rw [complete_recover]
        exact Ψ.property)⟩
  left_inv t := Subtype.ext (recover_complete M t.val)
  right_inv Ψ := Subtype.ext (complete_recover M Ψ.val)
  map_add' t s := Subtype.ext ((completionAddEquiv M).map_add t.val s.val)

variable [TopologicalSpace P] [IsTopologicalAddGroup P]

/-- Formula (4.8) on local full phase tables, including the continuous inverse
which sets all new cone coordinates to zero. -/
def localCompletionContinuousAddEquiv :
    localBulkSubgroup d D hD H hclosed hext actualLocal facets ≃ₜ+
      localCompletedSubgroup d D hD H hclosed hext actualLocal facets newFacets where
  toAddEquiv := localCompletionAddEquiv d D hD H hclosed hext actualLocal facets newFacets
    hcover hcolumns hrelative
  continuous_toFun := ((continuous_complete M).comp continuous_subtype_val).subtype_mk _
  continuous_invFun := ((continuous_recover M).comp continuous_subtype_val).subtype_mk _

end OpenDisk.BulkPhaseDifferentialModel
