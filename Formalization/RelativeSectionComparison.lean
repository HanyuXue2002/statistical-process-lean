import Formalization.RelativePrimitiveSection

set_option linter.style.header false

/-!
# The comparison theorem from relative primitive sections

`RelativePrimitiveSectionData` is the genuine mathematical input supplied by
the relative cochain argument (2.22)--(2.24).  This file is the public bridge
from that input to the comparison theorem.  The auxiliary
`PhysicalRelativeLiftData` is used only internally and never appears in any
statement below.

Thus a future simplicial-cochain module only has to construct the explicit
global sections and their visible-facet compatibility.  It can then invoke
`relativeSectionComparisonEquiv` directly; no second path-lifting hypothesis
or quotient argument remains to be supplied.
-/

noncomputable section

namespace GeneralSphereT.PathAlgebra

open FacetRestrictionData

universe uF uB uBA

variable {ι G : Type*} [LinearOrder ι] [AddCommGroup G]
variable {B : Type uB} [AddCommGroup B]
variable {Facet : Type uF} (facets : Facet → Set ι)
variable {BAt : Facet → Type uBA} [∀ ρ, AddCommGroup (BAt ρ)]
variable {d : Configuration ι G →+ B}

variable (L : FacetRestrictionData
  (CAt := fun ρ => Configuration (facets ρ) G)
  (BAt := BAt) (Facet := Facet) d)

namespace RelativePrimitiveSectionData

/-- The primitive-cycle representative obtained by taking the boundary of the
sectionwise relative lift. -/
def relativeSectionCycle
    (A : RelativePrimitiveSectionData facets L)
    (hprimitive : ∀ ρ : Facet,
      L.primitiveRes ρ = coordinateRestriction (facets ρ)) :
    physicalInvariantPaths L →ₗ[ℤ] Zprim L :=
  PhysicalRelativeLiftData.physicalToPrimitiveCycle facets L
    (toPhysicalRelativeLiftData facets L A hprimitive)

/-- Formula (2.34) before passing to the primitive quotient. -/
@[simp]
theorem relativeSectionCycle_coe
    (A : RelativePrimitiveSectionData facets L)
    (hprimitive : ∀ ρ : Facet,
      L.primitiveRes ρ = coordinateRestriction (facets ρ))
    (e : physicalInvariantPaths L) :
    ((relativeSectionCycle facets L A hprimitive e : Zprim L) :
        RedDist (Configuration ι G)) =
      primitiveReducedBoundary (Configuration ι G)
        (relativeLift facets L A
          (e : Path (Configuration ι G) B)) := by
  rfl

/-- The reverse comparison map (2.34), constructed from relative sections
rather than postulated path-lift data. -/
def relativeSectionReverseMap
    (A : RelativePrimitiveSectionData facets L)
    (hprimitive : ∀ ρ : Facet,
      L.primitiveRes ρ = coordinateRestriction (facets ρ))
    (hd : Function.Surjective d) :
    PhysicalQuotient L →ₗ[ℤ] TPrime L :=
  PhysicalRelativeLiftData.physicalToPrimitiveQuotient facets L
    (toPhysicalRelativeLiftData facets L A hprimitive) hd

/-- Representative formula for the reverse comparison map. -/
@[simp]
theorem relativeSectionReverseMap_mkQ
    (A : RelativePrimitiveSectionData facets L)
    (hprimitive : ∀ ρ : Facet,
      L.primitiveRes ρ = coordinateRestriction (facets ρ))
    (hd : Function.Surjective d) (e : physicalInvariantPaths L) :
    relativeSectionReverseMap facets L A hprimitive hd
        ((physicalIdentityPathsInInvariantPaths L).mkQ e) =
      (BprimInZprim L).mkQ
        (relativeSectionCycle facets L A hprimitive e) := by
  exact PhysicalRelativeLiftData.physicalToPrimitiveQuotient_mkQ
    facets L (toPhysicalRelativeLiftData facets L A hprimitive) hd e

/-- The forward comparison map (2.35), named here so the final simplicial API
can be used without referring to the implementation modules. -/
def relativeSectionForwardMap
    (hprimitive : ∀ ρ : Facet,
      L.primitiveRes ρ = coordinateRestriction (facets ρ))
    (hcover : ∀ i : ι, ∃ ρ : Facet, i ∈ facets ρ) :
    TPrime L →ₗ[ℤ] PhysicalQuotient L :=
  primitiveToPhysicalQuotient facets L hprimitive hcover

/-- Representative formula for the forward comparison map. -/
@[simp]
theorem relativeSectionForwardMap_mkQ
    (hprimitive : ∀ ρ : Facet,
      L.primitiveRes ρ = coordinateRestriction (facets ρ))
    (hcover : ∀ i : ι, ∃ ρ : Facet, i ∈ facets ρ)
    (s : Zprim L) :
    relativeSectionForwardMap facets L hprimitive hcover
        ((BprimInZprim L).mkQ s) =
      (physicalIdentityPathsInInvariantPaths L).mkQ
        (primitiveToPhysicalInvariant facets L hprimitive s) := by
  exact primitiveToPhysicalQuotient_mkQ
    facets L hprimitive hcover s

/-- Reverse after forward is the identity on `TPrime`. -/
theorem relativeSectionReverseMap_comp_forwardMap
    (A : RelativePrimitiveSectionData facets L)
    (hprimitive : ∀ ρ : Facet,
      L.primitiveRes ρ = coordinateRestriction (facets ρ))
    (hcover : ∀ i : ι, ∃ ρ : Facet, i ∈ facets ρ)
    (hd : Function.Surjective d) :
    (relativeSectionReverseMap facets L A hprimitive hd).comp
        (relativeSectionForwardMap facets L hprimitive hcover) =
      LinearMap.id := by
  exact
    PhysicalRelativeLiftData.physicalToPrimitiveQuotient_comp_primitiveToPhysicalQuotient
      facets L (toPhysicalRelativeLiftData facets L A hprimitive)
      hd hprimitive hcover

/-- Forward after reverse is the identity on the physical quotient. -/
theorem relativeSectionForwardMap_comp_reverseMap
    (A : RelativePrimitiveSectionData facets L)
    (hprimitive : ∀ ρ : Facet,
      L.primitiveRes ρ = coordinateRestriction (facets ρ))
    (hcover : ∀ i : ι, ∃ ρ : Facet, i ∈ facets ρ)
    (hd : Function.Surjective d) :
    (relativeSectionForwardMap facets L hprimitive hcover).comp
        (relativeSectionReverseMap facets L A hprimitive hd) =
      LinearMap.id := by
  exact
    PhysicalRelativeLiftData.primitiveToPhysicalQuotient_comp_physicalToPrimitiveQuotient
      facets L (toPhysicalRelativeLiftData facets L A hprimitive)
      hd hprimitive hcover

/--
The final objectwise comparison theorem from explicit relative sections.

This is the intended endpoint of the actual simplicial-cochain construction:
its only non-structural input is `RelativePrimitiveSectionData`, together with
the standard coboundary-surjectivity, literal-restriction, and facet-coverage
facts of that concrete model.
-/
def relativeSectionComparisonEquiv
    (A : RelativePrimitiveSectionData facets L)
    (hprimitive : ∀ ρ : Facet,
      L.primitiveRes ρ = coordinateRestriction (facets ρ))
    (hcover : ∀ i : ι, ∃ ρ : Facet, i ∈ facets ρ)
    (hd : Function.Surjective d) :
    PhysicalQuotient L ≃ₗ[ℤ] TPrime L :=
  PhysicalRelativeLiftData.physicalPrimitiveLinearEquiv facets L
    (toPhysicalRelativeLiftData facets L A hprimitive) hd hprimitive hcover

/-- Formula (2.34) as a representative computation for the final
equivalence. -/
@[simp]
theorem relativeSectionComparisonEquiv_apply_mkQ
    (A : RelativePrimitiveSectionData facets L)
    (hprimitive : ∀ ρ : Facet,
      L.primitiveRes ρ = coordinateRestriction (facets ρ))
    (hcover : ∀ i : ι, ∃ ρ : Facet, i ∈ facets ρ)
    (hd : Function.Surjective d) (e : physicalInvariantPaths L) :
    relativeSectionComparisonEquiv facets L A hprimitive hcover hd
        ((physicalIdentityPathsInInvariantPaths L).mkQ e) =
      (BprimInZprim L).mkQ
        (relativeSectionCycle facets L A hprimitive e) := by
  change relativeSectionReverseMap facets L A hprimitive hd
      ((physicalIdentityPathsInInvariantPaths L).mkQ e) = _
  exact relativeSectionReverseMap_mkQ facets L A hprimitive hd e

/-- Formula (2.35) as a representative computation for the inverse of the
final equivalence. -/
@[simp]
theorem relativeSectionComparisonEquiv_symm_apply_mkQ
    (A : RelativePrimitiveSectionData facets L)
    (hprimitive : ∀ ρ : Facet,
      L.primitiveRes ρ = coordinateRestriction (facets ρ))
    (hcover : ∀ i : ι, ∃ ρ : Facet, i ∈ facets ρ)
    (hd : Function.Surjective d) (s : Zprim L) :
    (relativeSectionComparisonEquiv facets L A hprimitive hcover hd).symm
        ((BprimInZprim L).mkQ s) =
      (physicalIdentityPathsInInvariantPaths L).mkQ
        (primitiveToPhysicalInvariant facets L hprimitive s) := by
  change relativeSectionForwardMap facets L hprimitive hcover
      ((BprimInZprim L).mkQ s) = _
  exact relativeSectionForwardMap_mkQ facets L hprimitive hcover s

/-! ## Independence of the chosen relative sections -/

/-- The sectionwise path lifts associated to two choices differ by a relation
path.  This is the representative-level source of canonicity. -/
theorem relativeLift_sub_relativeLift_mem_relationPaths
    (A₁ A₂ : RelativePrimitiveSectionData facets L)
    (hprimitive : ∀ ρ : Facet,
      L.primitiveRes ρ = coordinateRestriction (facets ρ))
    (e : physicalInvariantPaths L) :
    relativeLift facets L A₁
          (e : Path (Configuration ι G) B) -
        relativeLift facets L A₂
          (e : Path (Configuration ι G) B) ∈
      relationPaths L := by
  simpa [toPhysicalRelativeLiftData] using
    PhysicalRelativeLiftData.lift_sub_lift_mem_relationPaths facets L
      (toPhysicalRelativeLiftData facets L A₁ hprimitive)
      (toPhysicalRelativeLiftData facets L A₂ hprimitive) e

/-- The two boundary representatives differ by an element of `Bprim`. -/
theorem relativeSectionCycle_sub_mem_Bprim
    (A₁ A₂ : RelativePrimitiveSectionData facets L)
    (hprimitive : ∀ ρ : Facet,
      L.primitiveRes ρ = coordinateRestriction (facets ρ))
    (e : physicalInvariantPaths L) :
    (((relativeSectionCycle facets L A₁ hprimitive e -
          relativeSectionCycle facets L A₂ hprimitive e : Zprim L) :
        RedDist (Configuration ι G))) ∈ Bprim L := by
  exact PhysicalRelativeLiftData.physicalToPrimitiveCycle_sub_mem_Bprim
    facets L (toPhysicalRelativeLiftData facets L A₁ hprimitive)
      (toPhysicalRelativeLiftData facets L A₂ hprimitive) e

/-- Choice independence directly on quotient representatives. -/
theorem relativeSectionCycle_mkQ_independent
    (A₁ A₂ : RelativePrimitiveSectionData facets L)
    (hprimitive : ∀ ρ : Facet,
      L.primitiveRes ρ = coordinateRestriction (facets ρ))
    (e : physicalInvariantPaths L) :
    (BprimInZprim L).mkQ
        (relativeSectionCycle facets L A₁ hprimitive e) =
      (BprimInZprim L).mkQ
        (relativeSectionCycle facets L A₂ hprimitive e) := by
  apply (Submodule.Quotient.eq (BprimInZprim L)).2
  exact relativeSectionCycle_sub_mem_Bprim facets L A₁ A₂ hprimitive e

/-- The reverse comparison map is independent of the relative sections. -/
theorem relativeSectionReverseMap_independent
    (A₁ A₂ : RelativePrimitiveSectionData facets L)
    (hprimitive : ∀ ρ : Facet,
      L.primitiveRes ρ = coordinateRestriction (facets ρ))
    (hd : Function.Surjective d) :
    relativeSectionReverseMap facets L A₁ hprimitive hd =
      relativeSectionReverseMap facets L A₂ hprimitive hd := by
  exact
    PhysicalRelativeLiftData.physicalToPrimitiveQuotient_independent_of_lift
      facets L (toPhysicalRelativeLiftData facets L A₁ hprimitive)
        (toPhysicalRelativeLiftData facets L A₂ hprimitive) hd

/-- The final comparison equivalence is independent of every choice made in
the relative sections. -/
theorem relativeSectionComparisonEquiv_independent
    (A₁ A₂ : RelativePrimitiveSectionData facets L)
    (hprimitive : ∀ ρ : Facet,
      L.primitiveRes ρ = coordinateRestriction (facets ρ))
    (hcover : ∀ i : ι, ∃ ρ : Facet, i ∈ facets ρ)
    (hd : Function.Surjective d) :
    relativeSectionComparisonEquiv facets L A₁ hprimitive hcover hd =
      relativeSectionComparisonEquiv facets L A₂ hprimitive hcover hd := by
  exact
    PhysicalRelativeLiftData.physicalPrimitiveLinearEquiv_independent_of_lift
      facets L (toPhysicalRelativeLiftData facets L A₁ hprimitive)
        (toPhysicalRelativeLiftData facets L A₂ hprimitive)
          hd hprimitive hcover

end RelativePrimitiveSectionData

end GeneralSphereT.PathAlgebra
