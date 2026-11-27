import Formalization.Transport.ConePrismWitness
import Formalization.Transport.ConnectingEvaluation
import Formalization.Transport.ProjectedDifferential

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open CategoryTheory Opposite Simplicial AlgebraicTopology HomologicalComplex OpenDisk
namespace GeneralSphereT.Transport.Prism
open GeneralSphereT.SimplicialCochain GeneralSphereT.PathAlgebra FacetRestrictionData
open GeneralSphereT.StandardModels GeneralSphereT.Section4 RelativeChains

private theorem reduce_natural {U B : Type} [AddCommGroup U] [AddCommGroup B] (f : U →+ B) (z : PhaseDuality.Distribution U) :
    mapRedDist f (reduceDist z)=reduceDist (mapDistFn f z) := by
  have eq : (mapRedDist f).comp reduceDist=reduceDist.comp (mapDistFn f) := by
    apply Finsupp.lhom_ext'
    intro x
    apply LinearMap.ext_ring
    change mapRedDist f (reduceDist (Finsupp.single x 1))=reduceDist (mapDistFn f (Finsupp.single x 1))
    simp [reduceDist,mapRedDist_redBracket]
  exact LinearMap.congr_fun eq z

variable {V G : Type} [LinearOrder V] [Fintype V] [AddCommGroup G]
local instance connLE : LE (Option V) := @WithBot.instLE V inferInstance
local instance connLT : LT (Option V) := @WithBot.instLT V inferInstance
local instance connOrder : LinearOrder (Option V) := @WithBot.linearOrder V inferInstance
variable (X : AbstractSimplicialComplex V) (q d : ℕ) (E : ConeLifts (G:=G) X q)
variable (coeff : Simplex X d → ℤ) (hz : boundary (orientedFacets X d coeff)=0)

def signedFundamental : ChainSphere.cycles (altChains.obj (relFree (literalConeBottomSubcomplex X))) (d+1) :=
  ⟨alternatingConeCycle X d coeff,alternatingConeCycle_closed X d coeff hz⟩

/-- The oriented integral homology condition on the source pair alone. -/
def IsRelativeHomologySphere : Prop :=
  QuasiIso (ChainSphere.mapOfCycle _ (d+1) (signedFundamental X d coeff hz))

private abbrev S := altSequence (AddCommGrpCat.of G) q

def fiberCycle (z : Zprim (facetRestrictionData (G:=G) X q)) :
    ChainSphere.cycles (S (G:=G) q).X₁ (d+1) :=
  imageCycle (d+1) (altChains.map (linearize _ _ ((E.cycleExtension X q).nativeExtensionRelativeMap X q z)))
    (signedFundamental X d coeff hz)

theorem witness_lift_boundary (z : Zprim (facetRestrictionData (G:=G) X q)) :
    (S q).f.f (d+1) (fiberCycle X q d E coeff hz z).val =
      (S q).X₂.d (d+2) (d+1) (reduceDist (coneWitness X q d E coeff z.val)) := by
  apply Subtype.ext
  change nativeValue X q d E z (alternatingConeCycle X d coeff)=
    ((AlternatingFaceMapComplex.obj (reducedFree (L (AddCommGrpCat.of G) (q+1)))).d (d+2) (d+1)
      (reduceDist (coneWitness X q d E coeff z.val)) : RedDist (Disk G q (d+1))).val
  rw [reduce_boundary]
  change _=(reduceDist (diskBoundary (coneWitness X q d E coeff z.val))).val
  rw [coneWitness_boundary X q d E coeff hz z]
  exact congrArg Subtype.val (reduceDist_red ((S q).f.f (d+1) (fiberCycle X q d E coeff hz z).val)).symm

def projectedWitness (z : Zprim (facetRestrictionData (G:=G) X q)) : ChainSphere.cycles (S (G:=G) q).X₃ (d+2) := by
  let w := reduceDist (coneWitness X q d E coeff z.val)
  let y := (fiberCycle X q d E coeff hz z).val
  let s := S (G:=G) q
  refine ⟨s.g.f (d+2) w,?_⟩
  have h₁ := ConcreteCategory.congr_hom (s.g.comm (d+2) (d+1)) w
  have h₂ := congrArg (s.g.f (d+1)) (witness_lift_boundary X q d E coeff hz z).symm
  have h₃ := ConcreteCategory.congr_hom (HomologicalComplex.congr_hom s.zero (d+1)) y
  exact h₁.trans (h₂.trans h₃)

theorem projectedWitness_val (z : Zprim (facetRestrictionData (G:=G) X q)) :
    (projectedWitness X q d E coeff hz z).val=reduceDist (witnessProjection X q d E coeff z.val) :=
  reduce_natural ((GeneralSphereT.StandardModels.d (AddCommGrpCat.of G) (q+1)).app (op ⦋d+2⦌)).hom _

theorem connectedWitness (z : Zprim (facetRestrictionData (G:=G) X q)) :
    connectingEquiv (AddCommGrpCat.of G) q (d+1) (homologyClass _ (d+2) (projectedWitness X q d E coeff hz z))=
      homologyClass _ (d+1) (fiberCycle X q d E coeff hz z) :=
  connecting_on_lift (AddCommGrpCat.of G) q (d+1) _ (reduceDist (coneWitness X q d E coeff z.val)) _ rfl
    (witness_lift_boundary X q d E coeff hz z)

/-- The resulting transgression is an equivalence and on each representative
its inverse connecting image is the projected, oriented segment itself. -/
def processHomologyEquiv (b : V) (hc : ReducedCohomologyZeroAt (G:=G) X b q) (hl : LowerExact (G:=G) X b q)
    (hs : IsRelativeHomologySphere X d coeff hz) :
    SimplicialTPrime G X q ≃ₗ[ℤ] (S (G:=G) q).X₃.homology (d+2) :=
  (coneTransgression X q E b hc hl).trans ((altEvaluation _ _ (d+1) (signedFundamental X d coeff hz) hs).trans
    (connectingEquiv (AddCommGrpCat.of G) q (d+1)).symm)

theorem processHomologyEquiv_mk (b : V) (hc : ReducedCohomologyZeroAt (G:=G) X b q) (hl : LowerExact (G:=G) X b q)
    (hs : IsRelativeHomologySphere X d coeff hz) (z : Zprim (facetRestrictionData (G:=G) X q)) :
    processHomologyEquiv X q d E coeff hz b hc hl hs ((BprimInZprim _).mkQ z)=
      homologyClass _ (d+2) (projectedWitness X q d E coeff hz z) := by
  let δ := connectingEquiv (AddCommGrpCat.of G) q (d+1)
  apply δ.injective
  refine (δ.apply_symm_apply _).trans ?_
  let ev := altEvaluation (literalConeBottomSubcomplex X) (F (AddCommGrpCat.of G) (q+1)) (d+1) (signedFundamental X d coeff hz) hs
  exact (congrArg ev (coneTransgression_mk X q E b hc hl z)).trans
    ((altEvaluation_mk _ _ _ _ hs _).trans (connectedWitness X q d E coeff hz z).symm)

end GeneralSphereT.Transport.Prism

