import Formalization.Transport.CoherentConeLifts

/-! The cone extension used to integrate the prism also supplies the
representative of the native transgression on the same primitive cycle. -/
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open CategoryTheory Opposite Simplicial
namespace GeneralSphereT.Transport.Prism
open GeneralSphereT.SimplicialCochain GeneralSphereT.PathAlgebra GeneralSphereT.StandardModels
open GeneralSphereT.Section4 GeneralSphereT.Section4.NativeRelativeHomotopyGroup FacetRestrictionData
variable {G V : Type} [AddCommGroup G] [LinearOrder V] [Fintype V]
local instance trLE : LE (Option V) := @WithBot.instLE V inferInstance
local instance trLT : LT (Option V) := @WithBot.instLT V inferInstance
local instance trOrder : LinearOrder (Option V) := @WithBot.linearOrder V inferInstance
variable (X : AbstractSimplicialComplex V) (q : ℕ) (E : ConeLifts (G:=G) X q)

def ConeLifts.fiberwise : FiberwiseCochainLift (coboundaryToRange (G:=G) X q)
    (coboundaryToRange (G:=G) (simplicialCone X) q) (coneBottomFacetHom (G:=G) X q).primitiveMap where
  lift := E.lift
  physicalLift a := coboundaryToRange _ q (E.lift (liftState X q a))
  res_lift := E.bottom
  d_lift v := by
    let u := liftState X q (coboundaryToRange X q v)
    let z : ClosedShifts (G:=G) X q := ⟨v-u,by
      rw [LinearMap.mem_ker,map_sub,show coboundary X q u=coboundary X q v from liftState_spec X q _,sub_self]⟩
    obtain ⟨Z,hZ⟩ := E.shift z
    have e : E.lift v=E.lift u+Z.val := (show u+z.val=v by dsimp [z]; abel) ▸ hZ u
    apply Subtype.ext
    exact (congrArg (coboundary _ q) e).trans ((map_add _ _ _).trans (by rw [show coboundary _ q Z.val=0 from Z.property,add_zero]; rfl))

def ConeLifts.cycleExtension : ConeCycleExtensionData (G:=G) X q :=
  ConeCycleExtensionData.ofFiberwiseCochainLift X q (E.fiberwise X q)

private theorem extension_value (z : Zprim (facetRestrictionData (G:=G) X q)) :
    ((E.cycleExtension X q).extendCycle z).val=mapRedDistFn E.lift z.val := rfl

/-- On every cone simplex, the extension is the original integer distribution
pushed forward by the same lifts as in the segment integral. -/
theorem ConeLifts.extension_on_simplex (z : Zprim (facetRestrictionData (G:=G) X q))
    (Δ : SimplexCategoryᵒᵖ) (x : (orderedComplexSSet (simplicialCone X)).obj Δ) :
    (underlyingMap (Fι (AddCommGrpCat.of G) (q+1))).app Δ
      (((E.cycleExtension X q).nativeExtensionRelativeMap X q z).map.app Δ x) =
    mapRedDistFn (fun v => cochainLValue (simplicialCone X) q Δ x (E.lift v)) z.val := by
  have h := (E.cycleExtension X q).nativeExtensionRelativeMap_comp_inclusion X q z
  have e := ConcreteCategory.congr_hom (NatTrans.congr_app h Δ) x
  change _ = (globalCochainRestrictionMap (simplicialCone X) q ((E.cycleExtension X q).extendCycle z).val).app Δ x at e
  rw [globalCochainRestrictionMap_app_apply,extension_value] at e
  exact e.trans (mapRedDistFn_comp_apply E.lift (cochainLValue (simplicialCone X) q Δ x) z.val)

/-- The degree directly below the primitive degree uses reduced cohomology
when it exists. At degree zero the complex is pointed by the chosen vertex. -/
def LowerExact (b : V) (degree : ℕ) : Prop := match degree with
  | 0 => True
  | n+1 => ReducedCohomologyZeroAt (G:=G) X b n

def coneTransgression (b : V) (hc : ReducedCohomologyZeroAt (G:=G) X b q) (hl : LowerExact (G:=G) X b q) :
    SimplicialTPrime G X q ≃ₗ[ℤ] NativeConeQuotientHomotopyClasses X (F (AddCommGrpCat.of G) (q+1)) := by
  cases q with
  | zero => exact nativeTransgressionLinearEquivDegreeZero X b hc (E.cycleExtension X 0) (E.fiberwise X 0)
  | succ n => exact nativeTransgressionLinearEquivOfReduced X b n hc hl (E.cycleExtension X (n+1)) (E.fiberwise X (n+1))

theorem coneTransgression_mk (b : V) (hc : ReducedCohomologyZeroAt (G:=G) X b q) (hl : LowerExact (G:=G) X b q)
    (z : Zprim (facetRestrictionData (G:=G) X q)) :
    coneTransgression X q E b hc hl ((BprimInZprim _).mkQ z)=
      (((E.cycleExtension X q).nativeExtensionRelativeMap X q z)).homotopyClass := by
  cases q with
  | zero => exact nativeTransgressionLinearEquivDegreeZero_mkQ X b hc (E.cycleExtension X 0) (E.fiberwise X 0) z
  | succ n => exact nativeTransgressionLinearEquivOfReduced_mkQ X b n hc hl (E.cycleExtension X (n+1)) (E.fiberwise X (n+1)) z

end GeneralSphereT.Transport.Prism

