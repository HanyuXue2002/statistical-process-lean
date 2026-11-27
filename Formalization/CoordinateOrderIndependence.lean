import Formalization.PhysicalToPrimitiveQuotient

set_option linter.style.header false

/-!
# Independence of the coordinate order

The ordered canonical path used in the forward comparison map depends on a
chosen linear order of the coordinates before passing to the quotient.  This
module proves that the descended comparison map does not.

The proof deliberately avoids comparing two ordered paths cell by cell.  For
every coordinate order, the forward map is inverse to the same order-free
reverse map supplied by `PhysicalRelativeLiftData`.  Equivalently, the
comparison linear equivalences have definitionally the same forward map, so
extensionality and uniqueness of inverses identify them.
-/

noncomputable section

namespace GeneralSphereT.PathAlgebra

open FacetRestrictionData
open PhysicalRelativeLiftData

universe uF uB uBA

variable {ι G : Type*} [AddCommGroup G]
variable {B : Type uB} [AddCommGroup B]
variable {Facet : Type uF} (facets : Facet → Set ι)
variable {BAt : Facet → Type uBA} [∀ ρ, AddCommGroup (BAt ρ)]
variable {d : Configuration ι G →+ B}

variable (L : FacetRestrictionData
  (CAt := fun ρ => Configuration (facets ρ) G)
  (BAt := BAt) (Facet := Facet) d)

/-- The forward comparison map with its coordinate order made explicit. -/
def primitiveToPhysicalQuotientWithOrder
    (order : LinearOrder ι)
    (hprimitive : ∀ ρ : Facet,
      L.primitiveRes ρ = coordinateRestriction (facets ρ))
    (hcover : ∀ i : ι, ∃ ρ : Facet, i ∈ facets ρ) :
    TPrime L →ₗ[ℤ] PhysicalQuotient L := by
  letI : LinearOrder ι := order
  exact primitiveToPhysicalQuotient facets L hprimitive hcover

/-- The comparison equivalence with its coordinate order made explicit. -/
def physicalPrimitiveLinearEquivWithOrder
    (order : LinearOrder ι)
    (A : PhysicalRelativeLiftData facets L)
    (hd : Function.Surjective d)
    (hprimitive : ∀ ρ : Facet,
      L.primitiveRes ρ = coordinateRestriction (facets ρ))
    (hcover : ∀ i : ι, ∃ ρ : Facet, i ∈ facets ρ) :
    PhysicalQuotient L ≃ₗ[ℤ] TPrime L := by
  letI : LinearOrder ι := order
  exact physicalPrimitiveLinearEquiv facets L A hd hprimitive hcover

@[simp]
theorem physicalPrimitiveLinearEquivWithOrder_apply
    (order : LinearOrder ι)
    (A : PhysicalRelativeLiftData facets L)
    (hd : Function.Surjective d)
    (hprimitive : ∀ ρ : Facet,
      L.primitiveRes ρ = coordinateRestriction (facets ρ))
    (hcover : ∀ i : ι, ∃ ρ : Facet, i ∈ facets ρ)
    (q : PhysicalQuotient L) :
    physicalPrimitiveLinearEquivWithOrder facets L order A hd hprimitive hcover q =
      physicalToPrimitiveQuotient facets L A hd q := by
  rfl

@[simp]
theorem physicalPrimitiveLinearEquivWithOrder_symm_toLinearMap
    (order : LinearOrder ι)
    (A : PhysicalRelativeLiftData facets L)
    (hd : Function.Surjective d)
    (hprimitive : ∀ ρ : Facet,
      L.primitiveRes ρ = coordinateRestriction (facets ρ))
    (hcover : ∀ i : ι, ∃ ρ : Facet, i ∈ facets ρ) :
    (physicalPrimitiveLinearEquivWithOrder facets L order A hd hprimitive hcover).symm.toLinearMap =
      primitiveToPhysicalQuotientWithOrder facets L order hprimitive hcover := by
  rfl

/-- The comparison equivalence is independent of the chosen coordinate order. -/
theorem physicalPrimitiveLinearEquivWithOrder_independent
    (order₁ order₂ : LinearOrder ι)
    (A : PhysicalRelativeLiftData facets L)
    (hd : Function.Surjective d)
    (hprimitive : ∀ ρ : Facet,
      L.primitiveRes ρ = coordinateRestriction (facets ρ))
    (hcover : ∀ i : ι, ∃ ρ : Facet, i ∈ facets ρ) :
    physicalPrimitiveLinearEquivWithOrder facets L order₁ A hd hprimitive hcover =
      physicalPrimitiveLinearEquivWithOrder facets L order₂ A hd hprimitive hcover := by
  apply LinearEquiv.ext
  intro q
  rfl

/-- Formula (2.35), after passage to the quotient, is independent of the
coordinate order used to form the canonical path. -/
theorem primitiveToPhysicalQuotientWithOrder_independent
    (order₁ order₂ : LinearOrder ι)
    (A : PhysicalRelativeLiftData facets L)
    (hd : Function.Surjective d)
    (hprimitive : ∀ ρ : Facet,
      L.primitiveRes ρ = coordinateRestriction (facets ρ))
    (hcover : ∀ i : ι, ∃ ρ : Facet, i ∈ facets ρ) :
    primitiveToPhysicalQuotientWithOrder facets L order₁ hprimitive hcover =
      primitiveToPhysicalQuotientWithOrder facets L order₂ hprimitive hcover := by
  have hequiv := physicalPrimitiveLinearEquivWithOrder_independent
    facets L order₁ order₂ A hd hprimitive hcover
  have hinv := congrArg
    (fun e : PhysicalQuotient L ≃ₗ[ℤ] TPrime L => e.symm.toLinearMap)
    hequiv
  simpa only [physicalPrimitiveLinearEquivWithOrder_symm_toLinearMap] using hinv

end GeneralSphereT.PathAlgebra
