import Formalization.Transport.TopFacets
import Formalization.Transport.PrimitiveClassification
import Formalization.Transport.PhaseCohomology
import Formalization.Section4NativeMainTheorems

/-! Connecting the actual transport multiplication to the established
simplicial primitive quotient and its native pointed mapping-class presentation. -/
noncomputable section
namespace GeneralSphereT.Transport
open GeneralSphereT.PathAlgebra GeneralSphereT.PathAlgebra.FacetRestrictionData
open GeneralSphereT.SimplicialCochain OpenDisk.PhaseDuality GeneralSphereT.StandardModels
universe u
variable {V G : Type u} [LinearOrder V] [Fintype V] [AddCommGroup G]
variable (K : AbstractSimplicialComplex V) (d n : ℕ)
local instance (k : ℕ) : Fintype (Simplex K k) := Fintype.ofFinite _
local instance (k : ℕ) : LinearOrder (Simplex K k) := uniformSimplexColexOrder K k

abbrev TopMultiplierClasses := Quotient (localEquivalence (topFacetData (G:=G) K d n))

/-- Multipliers restricted to the literal top-dimensional simplices, paired
with the strict quotient indexed by all simplices as used by the sphere library. -/
def simplicialPrimitiveClassification (hp : PureInDimension K d) :
    TopMultiplierClasses (G:=G) K d n ≃ (SimplicialTPrime G K n →ₗ[ℤ] Phase) :=
  (primitiveClassification (topFacetData K d n) (fun _ => rfl) (topRelativeSections K d n)
    (facetCoboundary_surjective K n) (topCover K d n hp)).trans
    ((topPrimitiveEquiv (G:=G) K d n hp).arrowCongr (LinearEquiv.refl ℤ Phase)).toEquiv

theorem simplicialStrictification (hp : PureInDimension K d)
    (m : SimplicialMultiplier (G:=G) K d n) (χ : TPrime (topFacetData (G:=G) K d n) →ₗ[ℤ] Phase)
    (hm : Represents (topFacetData K d n) m χ) :
    Equivalent (topFacetData K d n) m.value (fun _ => 0) ↔ χ=0 := by
  let L := topFacetData (G:=G) K d n
  have zeroRep : Represents L (zeroMultiplier L) 0 := by
    refine ⟨fun _ _ => 0,?_,fun z => ?_⟩
    · funext x
      simp [zeroMultiplier,curvature]
    · change 0 = phaseTableEquiv (0 : Cochain K n G → Phase) z.val.val
      rw [map_zero,LinearMap.zero_apply]
  constructor
  · exact uniqueness_of_represents L (facetCoboundary_surjective K n) (topCover K d n hp) hm zeroRep
  · rintro rfl
    exact equivalent_of_represents L (fun _ => rfl) (topRelativeSections K d n) hm zeroRep

/-- Positive primitive degree; paper degree q = n+2. -/
def sphereLoopCharacterClassification (b : V) (hp : PureInDimension K d)
    (hi : ReducedCohomologyZeroAt (G:=G) K b (n+1)) (lo : ReducedCohomologyZeroAt (G:=G) K b n) :
    TopMultiplierClasses (G:=G) K d (n+1) ≃
      (OrientedSphereLoopPiPresentation K (F (AddCommGrpCat.of G) (n+2)) →ₗ[ℤ] Phase) :=
  (simplicialPrimitiveClassification K d (n+1) hp).trans
    ((nativeSphereTPrimeLoopPiPresentationOfReduced K b n hi lo).arrowCongr (LinearEquiv.refl ℤ Phase)).toEquiv

/-- Degree-zero primitives; paper degree q = 1. -/
def sphereLoopCharacterClassificationDegreeZero (b : V) (hp : PureInDimension K d)
    (h : ReducedCohomologyZeroAt (G:=G) K b 0) :
    TopMultiplierClasses (G:=G) K d 0 ≃
      (OrientedSphereLoopPiPresentation K (F (AddCommGrpCat.of G) 1) →ₗ[ℤ] Phase) :=
  (simplicialPrimitiveClassification K d 0 hp).trans
    ((nativeSphereTPrimeLoopPiPresentationDegreeZeroOfReduced K b h).arrowCongr (LinearEquiv.refl ℤ Phase)).toEquiv

end GeneralSphereT.Transport

