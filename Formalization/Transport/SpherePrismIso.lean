import Formalization.Transport.ConeConnectingClass
import Formalization.Transport.EMHomologyPairing
import Formalization.Transport.IntegralPrism
import Formalization.Transport.SphereComparison

/-! Identification of the triangle integral with the dual of the oriented
transgression. All hypotheses on the triangulation concern its source chains. -/
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
noncomputable section
open OpenDisk
namespace GeneralSphereT.Transport.Prism
open GeneralSphereT.SimplicialCochain GeneralSphereT.PathAlgebra FacetRestrictionData
open GeneralSphereT.StandardModels PhaseDuality RelativeChains
variable {V G : Type} [LinearOrder V] [Fintype V] [AddCommGroup G]
variable (X : AbstractSimplicialComplex V) (q d : ℕ) (b : V) (hp : PureInDimension X d)
variable (hc : ReducedCohomologyZeroAt (G:=G) X b q) (hl : LowerExact (G:=G) X b q)
variable (hall : ReducedCohomologyZeroAt (G:=ShiftEvaluations (G:=G) X q) X b q)
variable (coeff : Simplex X d → ℤ) (hz : boundary (orientedFacets X d coeff)=0)
variable (hs : IsRelativeHomologySphere X d coeff hz)
local instance (k : ℕ) : Fintype (Simplex X k) := Fintype.ofFinite _
local instance (k : ℕ) : LinearOrder (Simplex X k) := uniformSimplexColexOrder X k

private def topClasses :=
  primitiveClassification (topFacetData (G:=G) X d q) (fun _ => rfl) (topRelativeSections X d q)
    (facetCoboundary_surjective X q) (topCover X d q hp)

def orientedProcessEquiv : TPrime (topFacetData (G:=G) X d q) ≃ₗ[ℤ] CycleClasses (G:=G) (q+1) d :=
  (topPrimitiveEquiv X d q hp).trans ((processHomologyEquiv X q d (coherentConeLifts X q b hall) coeff hz b hc hl hs).trans
    (altEMEquiv (q+1) d))

theorem oriented_prism_pairing (a : NormalizedEMCohomology G (q+1) d) :
    topClasses X q d hp (prismClass X q d b hc coeff hz a)=
      (normalizedCharacterEquiv (q+1) d a).comp (orientedProcessEquiv X q d b hp hc hl hall coeff hz hs).toLinearMap := by
  induction a using Quotient.inductionOn with | _ ω =>
    let E := coherentConeLifts X q b hall
    obtain ⟨χ,hm,hχ⟩ := character_on_cone X q d E b hc ω.val ω.property.1 ω.property.2 coeff hz
    rw [prismClass_mk,topClasses,primitiveClassification_mk _ _ _ _ _ _ χ hm]
    apply LinearMap.ext
    intro y
    obtain ⟨z,rfl⟩ := (BprimInZprim _).mkQ_surjective y
    let z' : Zprim (facetRestrictionData (G:=G) X q) :=
      ⟨z.val,(topPrimitiveSubmodules (G:=G) X d q hp).1 ▸ z.property⟩
    rw [hχ]
    change _=cocycleCharacter (q+1) d ω (altEMEquiv (q+1) d
      (processHomologyEquiv X q d E coeff hz b hc hl hs (topPrimitiveEquiv X d q hp ((BprimInZprim _).mkQ z))))
    rw [topPrimitiveEquiv_mk,processHomologyEquiv_mk]
    refine Eq.trans ?_ (altEM_pairing (q+1) d ω (projectedWitness X q d E coeff hz z')).symm
    exact (witness_measures X q d E coeff z.val ω.val).symm.trans
      ((evaluate_reduction (q+1) d ω _).symm.trans
        (congrArg (fun x : RedDist (EM G (q+1) (d+2)) => evaluate ω.val x.val) (projectedWitness_val X q d E coeff hz z').symm))

include hp hl hall hs

/-- Bijectivity of the specified map of Eq. (2.8). -/
theorem prismClass_bijective :
    Function.Bijective (prismClass X q d b hc coeff hz) := by
  let e := orientedProcessEquiv X q d b hp hc hl hall coeff hz hs
  let dual : (CycleClasses (G:=G) (q+1) d →ₗ[ℤ] Phase) ≃ₗ[ℤ] (TPrime (topFacetData (G:=G) X d q) →ₗ[ℤ] Phase) := e.symm.arrowCongr (LinearEquiv.refl ℤ Phase)
  let p := prismClass X q d b hc coeff hz
  let T := topClasses (G:=G) X q d hp
  have eq : T ∘ p=dual ∘ normalizedCharacterEquiv (q+1) d :=
    funext (oriented_prism_pairing X q d b hp hc hl hall coeff hz hs)
  change Function.Bijective p
  rw [← Equiv.comp_bijective p T,eq]
  exact dual.bijective.comp (normalizedCharacterEquiv (q+1) d).bijective

/-- The equivalence acts by the signed triangle formula on every representative. -/
def spherePrismEquiv : NormalizedEMCohomology G (q+1) d ≃ TopMultiplierClasses (G:=G) X d q :=
  Equiv.ofBijective _ (prismClass_bijective X q d b hp hc hl hall coeff hz hs)

@[simp] theorem spherePrismEquiv_mk (ω : NormalizedCocycle G (q+1) d) :
    spherePrismEquiv X q d b hp hc hl hall coeff hz hs (Quotient.mk _ ω)=Quotient.mk _
      (physicalPrismMultiplier X q d b hc ω.val ω.property.1 ω.property.2 coeff hz) := rfl

/-- The integral process map is likewise a linear equivalence. -/
def integralPrismEquiv : IntegralProcesses (topFacetData (G:=G) X d q) ≃ₗ[ℤ] CycleClasses (G:=G) (q+1) d :=
  LinearEquiv.ofBijective _ ((prism_bijective_iff_integral X q d b hc coeff hz).mp
    (prismClass_bijective X q d b hp hc hl hall coeff hz hs))

end GeneralSphereT.Transport.Prism
