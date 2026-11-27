import Formalization.Transport.ConePrismCharacter

/-! A single universal cocycle supplies closed cone lifts simultaneously for all
closed shifts. The choices of representatives of exact states need no additivity. -/
set_option maxHeartbeats 1800000
noncomputable section
namespace GeneralSphereT.Transport.Prism
open GeneralSphereT.SimplicialCochain OrderedSimplicialMap
variable {G V : Type} [AddCommGroup G] [LinearOrder V] [Fintype V]
local instance liftLE : LE (Option V) := @WithBot.instLE V inferInstance
local instance liftLT : LT (Option V) := @WithBot.instLT V inferInstance
local instance liftOrder : LinearOrder (Option V) := @WithBot.linearOrder V inferInstance
variable (X : AbstractSimplicialComplex V) (q : ℕ)

abbrev ClosedShifts := LinearMap.ker (coboundary (G:=G) X q)
abbrev ShiftEvaluations := ClosedShifts (G:=G) X q →+ G

private def universalClosed : Cochain X q (ShiftEvaluations (G:=G) X q) :=
  Finsupp.equivFunOnFinite.symm fun σ => {
    toFun := fun v => v.val σ
    map_zero' := rfl
    map_add' := fun _ _ => rfl }

private theorem universalClosed_closed : coboundary X q (universalClosed (G:=G) X q)=0 := by
  ext σ v
  change (∑ i : σ.val, incidenceSign X σ i.val • universalClosed X q (eraseVertex X σ i.val i.property)) v=0
  simp only [AddMonoidHom.finsetSum_apply,AddMonoidHom.smul_apply]
  exact DFunLike.congr_fun (show coboundary X q v.val=0 from v.property) σ

private def evaluateExtension {U : Type} [AddCommGroup U] (z : U) (w : Cochain X q (U →+ G)) : Cochain X q G :=
  Finsupp.equivFunOnFinite.symm fun σ => w σ z

private theorem evaluateExtension_closed {U : Type} [AddCommGroup U] (z : U)
    (w : Cochain X q (U →+ G)) (hw : coboundary X q w=0) : coboundary X q (evaluateExtension X q z w)=0 := by
  ext σ
  have h := DFunLike.congr_fun (DFunLike.congr_fun hw σ) z
  simpa only [coboundary_apply,AddMonoidHom.finsetSum_apply,AddMonoidHom.smul_apply,
    Finsupp.zero_apply,AddMonoidHom.zero_apply,evaluateExtension,Finsupp.equivFunOnFinite_symm_apply_apply] using h

/-- Additive section of restriction on cocycles, obtained by evaluating one
extension with coefficients in the homomorphisms from the group of cocycles. -/
theorem exists_closed_section (b : V)
    (h : ReducedCohomologyZeroAt (G:=ShiftEvaluations (G:=G) X q) X b q) :
    ∃ S : ClosedShifts (G:=G) X q →+ ClosedShifts (G:=G) (simplicialCone X) q,
      ∀ z, (coneBottomInclusion X).pullback q (S z).val=z.val := by
  obtain ⟨w,hw,hr⟩ := closed_extension X q b h (universalClosed X q) (universalClosed_closed X q)
  refine ⟨{ toFun := fun z => ⟨evaluateExtension _ q z w,evaluateExtension_closed _ q z w hw⟩
            map_zero' := by apply Subtype.ext; ext σ; exact (w σ).map_zero
            map_add' := fun a b => by apply Subtype.ext; ext σ; exact (w σ).map_add a b },?_⟩
  intro z
  ext σ
  exact DFunLike.congr_fun (DFunLike.congr_fun hr σ) z

private def remainder (v : Cochain X q G) : ClosedShifts (G:=G) X q :=
  ⟨v - liftState X q (coboundaryToRange X q v), by
    rw [LinearMap.mem_ker,map_sub,liftState_spec]; exact sub_self _⟩

private theorem state_shift (v : Cochain X q G) (z : ClosedShifts (G:=G) X q) :
    coboundaryToRange X q (v+z.val)=coboundaryToRange X q v := by
  apply Subtype.ext
  exact (map_add (coboundary X q) v z.val).trans (by rw [show coboundary X q z.val=0 from z.property,add_zero]; rfl)

private def rawConeLift (S : ClosedShifts (G:=G) X q →+ ClosedShifts (G:=G) (simplicialCone X) q) (v : Cochain X q G) :=
  (coneBottomInclusion X).extendCochainByZero q (liftState X q (coboundaryToRange X q v)) + (S (remainder X q v)).val

/-- Equivariant, zero-preserving extensions used in the actual triangle integral. -/
def coherentConeLifts (b : V) (h : ReducedCohomologyZeroAt (G:=ShiftEvaluations (G:=G) X q) X b q) :
    ConeLifts (G:=G) X q := by
  let S := (exists_closed_section X q b h).choose
  have hr (z : ClosedShifts (G:=G) X q) : (coneBottomInclusion X).pullback q (S z).val=z.val :=
    (exists_closed_section X q b h).choose_spec z
  have bottom (v : Cochain X q G) : (coneBottomInclusion X).pullback q (rawConeLift X q S v)=v := by
    unfold rawConeLift
    rw [map_add,pullback_extendCochainByZero,show (coneBottomInclusion X).pullback q (S (remainder X q v)).val=_ from hr _]
    change _+(v-_)=v
    abel
  refine { lift := fun v => rawConeLift X q S v - rawConeLift X q S 0
           bottom := fun v => by rw [map_sub,bottom,bottom,sub_zero]
           zero := sub_self _
           shift := ?_ }
  intro z
  refine ⟨S z,fun v => ?_⟩
  have rem : remainder X q (v+z.val)=remainder X q v+z := by
    apply Subtype.ext
    change v+z.val-liftState X q (coboundaryToRange X q (v+z.val))=(v-liftState X q (coboundaryToRange X q v))+z.val
    rw [state_shift]; abel
  change rawConeLift X q S (v+z.val) - _ = _
  have eq : rawConeLift X q S (v+z.val)=rawConeLift X q S v+(S z).val := by
    unfold rawConeLift
    rw [state_shift,rem,map_add,Submodule.coe_add,add_assoc]
  rw [eq]; abel

local instance coherentFacet (d : ℕ) : Fintype (Simplex X d) := Fintype.ofFinite _
local instance coherentSimplexOrder (k : ℕ) : LinearOrder (Simplex X k) := uniformSimplexColexOrder X k

/-- Representative formula without a choice of simultaneous lifts as input. -/
theorem oriented_character (b : V) (hred : ReducedCohomologyZeroAt (G:=G) X b q)
    (hall : ReducedCohomologyZeroAt (G:=ShiftEvaluations (G:=G) X q) X b q)
    (d : ℕ) (ω : EM G (q+1) (d+2) → OpenDisk.PhaseDuality.Phase) (hc : ClosedOnEM ω) (hn : NormalizedOnEM ω)
    (coeff : Simplex X d → ℤ) (hz : boundary (orientedFacets X d coeff)=0) :
    let L := topFacetData (G:=G) X d q
    let m := physicalPrismMultiplier X q d b hred ω hc hn coeff hz
    ∃ χ : GeneralSphereT.PathAlgebra.FacetRestrictionData.TPrime L →ₗ[ℤ] OpenDisk.PhaseDuality.Phase,
      Represents L m χ ∧ ∀ z : GeneralSphereT.PathAlgebra.FacetRestrictionData.Zprim L,
        χ ((GeneralSphereT.PathAlgebra.FacetRestrictionData.BprimInZprim L).mkQ z)=
          OpenDisk.PhaseDuality.evaluate (fun v => coneEdge X q d ω coeff 0 ((coherentConeLifts X q b hall).lift v)) z.val.val :=
  character_on_cone X q d (coherentConeLifts X q b hall) b hred ω hc hn coeff hz

end GeneralSphereT.Transport.Prism

