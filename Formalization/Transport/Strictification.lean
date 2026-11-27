import Formalization.Transport.SphereComparison

noncomputable section
namespace GeneralSphereT.Transport
open GeneralSphereT.PathAlgebra OpenDisk.PhaseDuality GeneralSphereT.SimplicialCochain
variable {V G : Type} [LinearOrder V] [Fintype V] [AddCommGroup G]
variable (X : AbstractSimplicialComplex V) (d n : ℕ)
local instance (k : ℕ) : Fintype (Simplex X k) := Fintype.ofFinite _
local instance (k : ℕ) : LinearOrder (Simplex X k) := uniformSimplexColexOrder X k

/-- The strictification criterion stated for the character actually returned
by the simplicial classification, without supplying a splitting or character. -/
theorem strictification_iff_class_zero (hp : PureInDimension X d) (m : SimplicialMultiplier (G:=G) X d n) :
    Equivalent (topFacetData X d n) m.value (fun _ => 0) ↔
      simplicialPrimitiveClassification X d n hp (Quotient.mk _ m) = 0 := by
  let L := topFacetData (G:=G) X d n
  let e := primitiveClassification L (fun _ => rfl) (topRelativeSections X d n)
    (facetCoboundary_surjective X n) (topCover X d n hp)
  let h := e (Quotient.mk _ m)
  have rep : Represents L m h := by
    apply Classical.choose_spec
  have hs := simplicialStrictification X d n hp m h rep
  let A : (FacetRestrictionData.TPrime L →ₗ[ℤ] Phase) ≃ₗ[ℤ] (SimplicialTPrime G X n →ₗ[ℤ] Phase) :=
    (topPrimitiveEquiv (G:=G) X d n hp).arrowCongr (LinearEquiv.refl ℤ Phase)
  change Equivalent L m.value (fun _ => 0) ↔ A h = 0
  rw [A.map_eq_zero_iff]
  exact hs

/-- Comparison with the original elementary operator process quotient, with
its previously checked numerator of invariant paths and denominator of identities. -/
def originalProcessCharacterClassification (hp : PureInDimension X d) :
    TopMultiplierClasses (G:=G) X d n ≃
      (PhysicalQuotient (facetRestrictionData (G:=G) X n) →ₗ[ℤ] Phase) :=
  (simplicialPrimitiveClassification X d n hp).trans
    ((physicalPrimitiveComparisonEquiv (G:=G) X n).symm.arrowCongr (LinearEquiv.refl ℤ Phase)).toEquiv

end GeneralSphereT.Transport

