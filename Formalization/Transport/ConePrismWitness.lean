import Formalization.Transport.ConePrismFaces
import Formalization.Transport.ConePrismBoundary

/-! The actual lift in the connecting-homomorphism calculation. Its projection
is measured by the cone character; its boundary is the native transgression
evaluated at the relative oriented fundamental chain. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open CategoryTheory Opposite Simplicial
namespace GeneralSphereT.Transport.Prism
open GeneralSphereT.SimplicialCochain GeneralSphereT.PathAlgebra FacetRestrictionData
open GeneralSphereT.StandardModels GeneralSphereT.Section4 RelativeChains OpenDisk.PhaseDuality
variable {V G : Type} [LinearOrder V] [Fintype V] [AddCommGroup G]
local instance witnessLE : LE (Option V) := @WithBot.instLE V inferInstance
local instance witnessLT : LT (Option V) := @WithBot.instLT V inferInstance
local instance witnessOrder : LinearOrder (Option V) := @WithBot.linearOrder V inferInstance
variable (X : AbstractSimplicialComplex V) (q d : ℕ) (E : ConeLifts (G:=G) X q)
local instance witnessFintype : Fintype (Simplex X d) := Fintype.ofFinite _

def coneWitness (coeff : Simplex X d → ℤ) (z : RedDist (Cochain X q G)) :=
  assemble (fun v => liftedSegment X q d coeff 0 (E.lift v)) z.val

def witnessProjection (coeff : Simplex X d → ℤ) (z : RedDist (Cochain X q G)) :=
  mapDistFn ((GeneralSphereT.StandardModels.d (AddCommGrpCat.of G) (q+1)).app (op ⦋d+2⦌)) (coneWitness X q d E coeff z)

theorem witness_measures (coeff : Simplex X d → ℤ) (z : RedDist (Cochain X q G)) (ω : EM G (q+1) (d+2) → Phase) :
    evaluate ω (witnessProjection X q d E coeff z)=evaluate (fun v => coneEdge X q d ω coeff 0 (E.lift v)) z.val := by
  unfold witnessProjection coneWitness
  rw [assemble_map,assemble_map]
  exact congrArg (fun h : Cochain X q G → Phase => assemble h z.val)
    (funext (fun v => liftedSegment_projects X q d coeff 0 (E.lift v) ω))

def nativeValue (z : Zprim (facetRestrictionData (G:=G) X q)) :
    level (literalConeBottomSubcomplex X) (op ⦋d+1⦌) →ₗ[ℤ] Distribution (Disk G q (d+1)) :=
  (RedDist _).subtype.comp (((Fι (AddCommGrpCat.of G) (q+1)).app (op ⦋d+1⦌)).hom.toIntLinearMap.comp
    ((linearize _ _ ((E.cycleExtension X q).nativeExtensionRelativeMap X q z)).app (op ⦋d+1⦌)).hom.toIntLinearMap)

private theorem on_facet (σ : Simplex X d) (z : Zprim (facetRestrictionData (G:=G) X q)) :
    nativeValue X q d E z (relativeRead (simplicialCone X) (literalConeBottomSubcomplex X) (d+1) (gen (List.ofFn (coneVertices X d σ)))) =
      assemble (fun v => diskChain (affineField (simplicialCone X) q) (d+1)
        (vertices (layerOf _ q (E.lift v)) (gen (List.ofFn (coneVertices X d σ))))) z.val.val := by
  classical
  let x := coneVertices X d σ
  have hs := coneVertices_strict X d σ
  have hm := coneVertices_mem X d σ
  let h : Admissible (simplicialCone X) x := ⟨hs.monotone,hm⟩
  let a := orderedString (simplicialCone X) x h
  let f := (E.cycleExtension X q).nativeExtensionRelativeMap X q z
  rw [relativeRead_ofFn,relativeString,dite_eq_left h]
  have l := linearize_symbol (literalConeBottomSubcomplex X) (F (AddCommGrpCat.of G) (q+1)) f a
  have val := E.extension_on_simplex X q z (op ⦋d+1⦌) a
  have e := (congrArg (fun k => ((Fι (AddCommGrpCat.of G) (q+1)).app (op ⦋d+1⦌) k).val) l).trans (congrArg Subtype.val val)
  change _=(mapRedDistFn (fun v => cochainLValue (simplicialCone X) q (op ⦋d+1⦌) a (E.lift v)) z.val).val at e
  refine e.trans ?_
  rw [mapRedDistFn_coe]
  have eq : mapDistFn (fun v => cochainLValue (simplicialCone X) q (op ⦋d+1⦌) a (E.lift v))=
      assemble (fun v => diskChain (affineField (simplicialCone X) q) (d+1) (vertices (layerOf _ q (E.lift v)) (gen (List.ofFn x)))) := by
    apply Finsupp.lhom_ext'
    intro v
    apply LinearMap.ext_ring
    change mapDistFn _ (Finsupp.single v 1)=Finsupp.linearCombination ℤ _ (Finsupp.single v 1)
    rw [mapDistFn_single,Finsupp.linearCombination_single,one_smul,vertices_gen,List.map_ofFn,diskChain_ofFn]
    exact congrArg (fun a => Finsupp.single a (1:ℤ)) (constant_diskValue _ q (d+1) (E.lift v) x hs hm).symm
  exact LinearMap.congr_fun eq z.val.val

theorem coneWitness_boundary (coeff : Simplex X d → ℤ) (hz : boundary (orientedFacets X d coeff)=0)
    (z : Zprim (facetRestrictionData (G:=G) X q)) :
    diskBoundary (coneWitness X q d E coeff z.val)=nativeValue X q d E z (alternatingConeCycle X d coeff) := by
  rw [coneWitness,assembled_boundary X q d E coeff hz z,alternatingConeCycle,orientedCone_sum]
  simp only [map_sum,map_smul]
  rw [assemble_sum]
  apply Finset.sum_congr rfl
  intro σ _
  exact congrArg (fun a : Distribution (Disk G q (d+1)) => coeff σ • a) (on_facet X q d E σ z).symm

end GeneralSphereT.Transport.Prism

