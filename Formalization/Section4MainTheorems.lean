import Formalization.Section4DegreeZeroRow
import Formalization.Section4TopologicalComparisons

set_option linter.style.header false

/-!
# Section 4: legacy generic composition layer

This file retains the model-independent assembly lemmas for Propositions 4.3
and 4.5 and the suspension theorem.  Their domains are the concrete algebraic
groups `Tau facets L` and `TPrime L`, while the mapping-class targets and the
geometric maps are supplied abstractly so that the quotient algebra can be
reused in other models.

The explicit inputs have geometric meaning and no hidden algebra:
`hnull` is the cone criterion (4.6), `extensionClass` is (4.15), its kernel
and surjectivity are the relative two-cone argument, and
`twoConeDifference` is pointed cofiber exactness (4.25).

For the paper's literal ordered-complex and Dold--Kan models, this is no
longer the public endpoint: `Section4NativeMainTheorems` constructs these
geometric inputs internally and states (4.24)--(4.26) directly in Mathlib's
native simplicial homotopy-class groups.
-/

noncomputable section

namespace GeneralSphereT.PathAlgebra

open GeneralSphereT.Section4

universe uF uC uB uA uRel

namespace FacetRestrictionData

section Theta

variable {ι G : Type*} [LinearOrder ι] [AddCommGroup G]
variable {BPhys : Type uB} [AddCommGroup BPhys]
variable {Facet : Type uF} (facets : Facet → Set ι)
variable {BAt : Facet → Type uC} [∀ ρ, AddCommGroup (BAt ρ)]
variable {d : Configuration ι G →+ BPhys}

variable (L : FacetRestrictionData
  (CAt := fun ρ => Configuration (facets ρ) G)
  (BAt := BAt) (Facet := Facet) d)

/-- Proposition 4.3 in the concrete degree-zero row.  The equality `hnull`
is precisely (4.6), proved geometrically from fiberwise extension and cone
vanishing. -/
def thetaOfConeCriterion
    {A : Type uA} [AddCommGroup A]
    (based : BasedRowData A (zprimToRprim L) (restrictionClass L))
    (himage :
      Submodule.map (mapRedDist d) (locallyZeroRedDist L) =
        physicalNonfaceCubeSpan facets d)
    (hsurj : Function.Surjective (mapRedDist d))
    (NullMaps : Submodule ℤ based.BasedSections)
    (hnull : LinearMap.range based.basedRestriction = NullMaps) :
    Tau facets L ≃ₗ[ℤ]
      PointedHomotopyClasses based.BasedSections NullMaps :=
  theta based NullMaps
    (exact_restrictionClass_obstruction facets L himage)
    (obstruction_surjective facets L himage hsurj)
    hnull

omit [LinearOrder ι] in
/-- Formula (4.14) for the concrete obstruction row. -/
@[simp]
theorem thetaOfConeCriterion_obstruction
    {A : Type uA} [AddCommGroup A]
    (based : BasedRowData A (zprimToRprim L) (restrictionClass L))
    (himage :
      Submodule.map (mapRedDist d) (locallyZeroRedDist L) =
        physicalNonfaceCubeSpan facets d)
    (hsurj : Function.Surjective (mapRedDist d))
    (NullMaps : Submodule ℤ based.BasedSections)
    (hnull : LinearMap.range based.basedRestriction = NullMaps)
    (f : based.BasedSections) :
    thetaOfConeCriterion facets L based himage hsurj NullMaps hnull
        (based.basedObstruction (obstruction facets L himage) f) =
      NullMaps.mkQ f := by
  exact theta_obstruction based NullMaps
    (exact_restrictionClass_obstruction facets L himage)
    (obstruction_surjective facets L himage hsurj) hnull f

end Theta

section Transgression

variable {C : Type uC} {BPhys : Type uB}
variable [AddCommGroup C] [AddCommGroup BPhys]
variable {Facet : Type uF}
variable {CAt : Facet → Type*} {BAt : Facet → Type*}
variable [∀ ρ, AddCommGroup (CAt ρ)] [∀ ρ, AddCommGroup (BAt ρ)]
variable {d : C →+ BPhys}
variable (L : FacetRestrictionData
  (CAt := CAt) (BAt := BAt) (Facet := Facet) d)
variable {Rel : Type uRel} [AddCommGroup Rel]

/-- Proposition 4.5 specialized to the literal primitive quotient
`TPrime L = Zprim L / Bprim L`. -/
def transgressionOfConeExtension
    (extensionClass : Zprim L →ₗ[ℤ] Rel)
    (hker : LinearMap.ker extensionClass = BprimInZprim L)
    (hsurj : Function.Surjective extensionClass) :
    TPrime L ≃ₗ[ℤ] Rel :=
  transgression (BprimInZprim L) extensionClass hker hsurj

/-- Formula (4.18) on a primitive cycle representative. -/
@[simp]
theorem transgressionOfConeExtension_mkQ
    (extensionClass : Zprim L →ₗ[ℤ] Rel)
    (hker : LinearMap.ker extensionClass = BprimInZprim L)
    (hsurj : Function.Surjective extensionClass) (s : Zprim L) :
    transgressionOfConeExtension L extensionClass hker hsurj
        ((BprimInZprim L).mkQ s) =
      extensionClass s :=
  transgression_mkQ (BprimInZprim L) extensionClass hker hsurj s

/-- The suspension theorem (4.26), with `TPrime L` as its actual source.
The order of composition fixes the paper's lower-cone-minus-upper-cone sign. -/
def suspensionTheorem
    {SuspMaps TauSusp : Type*}
    [AddCommGroup SuspMaps] [AddCommGroup TauSusp]
    (extensionClass : Zprim L →ₗ[ℤ] Rel)
    (hker : LinearMap.ker extensionClass = BprimInZprim L)
    (hsurj : Function.Surjective extensionClass)
    (twoConeDifference : SuspMaps ≃ₗ[ℤ] Rel)
    (thetaSusp : TauSusp ≃ₗ[ℤ] SuspMaps) :
    TPrime L ≃ₗ[ℤ] TauSusp :=
  suspensionComparison
    (transgressionOfConeExtension L extensionClass hker hsurj)
    twoConeDifference thetaSusp

@[simp]
theorem suspensionTheorem_apply
    {SuspMaps TauSusp : Type*}
    [AddCommGroup SuspMaps] [AddCommGroup TauSusp]
    (extensionClass : Zprim L →ₗ[ℤ] Rel)
    (hker : LinearMap.ker extensionClass = BprimInZprim L)
    (hsurj : Function.Surjective extensionClass)
    (twoConeDifference : SuspMaps ≃ₗ[ℤ] Rel)
    (thetaSusp : TauSusp ≃ₗ[ℤ] SuspMaps) (x : TPrime L) :
    suspensionTheorem L extensionClass hker hsurj
        twoConeDifference thetaSusp x =
      thetaSusp.symm
        (twoConeDifference.symm
          (transgressionOfConeExtension L extensionClass hker hsurj x)) :=
  rfl

end Transgression

end FacetRestrictionData

end GeneralSphereT.PathAlgebra
