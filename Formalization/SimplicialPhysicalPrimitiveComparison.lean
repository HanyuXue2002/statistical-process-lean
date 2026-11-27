import Formalization.SimplicialRelativePrimitiveDataZero
import Formalization.SimplicialRelativePrimitiveDataSucc

set_option linter.style.header false

/-!
# The simplicial physical--primitive comparison in every degree

This module is the degree-uniform entry point for the concrete comparison
theorem.  Degree zero uses the augmentation-corrected primitive, while a
successor degree uses the positive-degree closed-star correction.
-/

noncomputable section

namespace GeneralSphereT.SimplicialCochain

open GeneralSphereT.PathAlgebra
open GeneralSphereT.PathAlgebra.FacetRestrictionData
open GeneralSphereT.PathAlgebra.RelativePrimitiveSectionData

variable {V G : Type*} [LinearOrder V] [Fintype V] [AddCommGroup G]
variable (K : AbstractSimplicialComplex V)

/-- The vertex order induces the colexicographic coordinate order in every
cochain degree. -/
local instance uniformSimplexColexOrder (n : ℕ) : LinearOrder (Simplex K n) :=
  LinearOrder.lift'
    (fun η : Simplex K n => toColex η.1)
    ((toColex : Finset V ≃ Colex (Finset V)).injective.comp
      Subtype.val_injective)

/-- Relative primitive sections, uniformly in the cochain degree. -/
def simplicialRelativePrimitiveSectionData (n : ℕ) :
    RelativePrimitiveSectionData
      (fun σ : NonemptySimplex K => facesIn K n σ)
      (facetRestrictionData (G := G) K n) :=
  match n with
  | 0 => relativePrimitiveSectionDataZero K
  | m + 1 => relativePrimitiveSectionDataSucc K m

@[simp]
theorem simplicialRelativePrimitiveSectionData_zero :
    simplicialRelativePrimitiveSectionData (G := G) K 0 =
      relativePrimitiveSectionDataZero K :=
  rfl

@[simp]
theorem simplicialRelativePrimitiveSectionData_succ (m : ℕ) :
    simplicialRelativePrimitiveSectionData (G := G) K (m + 1) =
      relativePrimitiveSectionDataSucc K m :=
  rfl

/-- The concrete physical--primitive comparison in arbitrary cochain degree. -/
def physicalPrimitiveComparisonEquiv (n : ℕ) :
    PhysicalQuotient (facetRestrictionData (G := G) K n) ≃ₗ[ℤ]
      TPrime (facetRestrictionData (G := G) K n) :=
  match n with
  | 0 => physicalPrimitiveComparisonEquivZero K
  | m + 1 => physicalPrimitiveComparisonEquivSucc K m

@[simp]
theorem physicalPrimitiveComparisonEquiv_zero :
    physicalPrimitiveComparisonEquiv (G := G) K 0 =
      physicalPrimitiveComparisonEquivZero K :=
  rfl

@[simp]
theorem physicalPrimitiveComparisonEquiv_succ (m : ℕ) :
    physicalPrimitiveComparisonEquiv (G := G) K (m + 1) =
      physicalPrimitiveComparisonEquivSucc K m :=
  rfl

/-- Formula (2.34) for the degree-uniform comparison on a physical
invariant-path representative. -/
@[simp]
theorem physicalPrimitiveComparisonEquiv_apply_mkQ (n : ℕ)
    (e : physicalInvariantPaths (facetRestrictionData (G := G) K n)) :
    physicalPrimitiveComparisonEquiv K n
        ((physicalIdentityPathsInInvariantPaths
          (facetRestrictionData (G := G) K n)).mkQ e) =
      (BprimInZprim (facetRestrictionData (G := G) K n)).mkQ
        (relativeSectionCycle
          (fun σ : NonemptySimplex K => facesIn K n σ)
          (facetRestrictionData (G := G) K n)
          (simplicialRelativePrimitiveSectionData K n)
          (facetRestrictionData_primitiveRes (G := G) K n) e) := by
  cases n with
  | zero =>
      exact relativeSectionComparisonEquiv_apply_mkQ
        (fun σ : NonemptySimplex K => facesIn K 0 σ)
        (facetRestrictionData (G := G) K 0)
        (relativePrimitiveSectionDataZero K)
        (facetRestrictionData_primitiveRes (G := G) K 0)
        (facetRestrictionData_cover K 0)
        (facetCoboundary_surjective (G := G) K 0) e
  | succ m =>
      exact relativeSectionComparisonEquiv_apply_mkQ
        (fun σ : NonemptySimplex K => facesIn K (m + 1) σ)
        (facetRestrictionData (G := G) K (m + 1))
        (relativePrimitiveSectionDataSucc K m)
        (facetRestrictionData_primitiveRes (G := G) K (m + 1))
        (facetRestrictionData_cover K (m + 1))
        (facetCoboundary_surjective (G := G) K (m + 1)) e

/-- Formula (2.35) for the inverse comparison on a primitive-cycle
representative. -/
@[simp]
theorem physicalPrimitiveComparisonEquiv_symm_apply_mkQ (n : ℕ)
    (s : Zprim (facetRestrictionData (G := G) K n)) :
    (physicalPrimitiveComparisonEquiv K n).symm
        ((BprimInZprim (facetRestrictionData (G := G) K n)).mkQ s) =
      (physicalIdentityPathsInInvariantPaths
        (facetRestrictionData (G := G) K n)).mkQ
        (primitiveToPhysicalInvariant
          (fun σ : NonemptySimplex K => facesIn K n σ)
          (facetRestrictionData (G := G) K n)
          (facetRestrictionData_primitiveRes (G := G) K n) s) := by
  cases n with
  | zero =>
      exact relativeSectionComparisonEquiv_symm_apply_mkQ
        (fun σ : NonemptySimplex K => facesIn K 0 σ)
        (facetRestrictionData (G := G) K 0)
        (relativePrimitiveSectionDataZero K)
        (facetRestrictionData_primitiveRes (G := G) K 0)
        (facetRestrictionData_cover K 0)
        (facetCoboundary_surjective (G := G) K 0) s
  | succ m =>
      exact relativeSectionComparisonEquiv_symm_apply_mkQ
        (fun σ : NonemptySimplex K => facesIn K (m + 1) σ)
        (facetRestrictionData (G := G) K (m + 1))
        (relativePrimitiveSectionDataSucc K m)
        (facetRestrictionData_primitiveRes (G := G) K (m + 1))
        (facetRestrictionData_cover K (m + 1))
        (facetCoboundary_surjective (G := G) K (m + 1)) s

end GeneralSphereT.SimplicialCochain
