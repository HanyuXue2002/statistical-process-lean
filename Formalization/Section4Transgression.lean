import Formalization.Section4TopologicalComparisons

set_option linter.style.header false

/-!
# Section 4: the four checks for the transgression

After the extension-class map of (4.18) has been constructed, its proof is
best organized by the three algebraic facts actually used: relation
boundaries give the zero relative class, a zero relative class is a relation
boundary (the double-cone argument), and every relative class is represented.
This file turns those statements into the claimed quotient equivalence and
keeps the representative formula definitional.
-/

noncomputable section

namespace GeneralSphereT.Section4

universe uZ uRel

variable {Z : Type uZ} {Rel : Type uRel}
variable [AddCommGroup Z] [AddCommGroup Rel]

section RelativeQuotient

universe uMaps

variable {Maps : Type uMaps} [AddCommGroup Maps]

/-- Send an extension map to its relative homotopy class by quotienting out
the subgroup of relatively nullhomotopic maps. -/
def relativeClassMap
    (NullMaps : Submodule ℤ Maps) (extensionMap : Z →ₗ[ℤ] Maps) :
    Z →ₗ[ℤ] (Maps ⧸ NullMaps) :=
  NullMaps.mkQ.comp extensionMap

@[simp]
theorem relativeClassMap_apply
    (NullMaps : Submodule ℤ Maps) (extensionMap : Z →ₗ[ℤ] Maps)
    (z : Z) :
    relativeClassMap NullMaps extensionMap z =
      NullMaps.mkQ (extensionMap z) :=
  rfl

/-- The contraction argument in the denominator paragraph only has to show
that every relation boundary is sent into `NullMaps`; quotient algebra then
puts the entire boundary submodule in the kernel. -/
theorem boundarySubmodule_le_ker_relativeClassMap
    (B : Submodule ℤ Z) (NullMaps : Submodule ℤ Maps)
    (extensionMap : Z →ₗ[ℤ] Maps)
    (hnull : B ≤ Submodule.comap extensionMap NullMaps) :
    B ≤ LinearMap.ker (relativeClassMap NullMaps extensionMap) := by
  intro z hz
  rw [LinearMap.mem_ker, relativeClassMap_apply]
  exact (Submodule.Quotient.mk_eq_zero NullMaps).2 (hnull hz)

end RelativeQuotient

/-- The three conclusions of the geometric part of Proposition 4.5. -/
structure TransgressionProofData
    (B : Submodule ℤ Z) (extensionClass : Z →ₗ[ℤ] Rel) where
  boundaries_null : B ≤ LinearMap.ker extensionClass
  relative_zero_is_boundary : LinearMap.ker extensionClass ≤ B
  representative_exists : Function.Surjective extensionClass

namespace TransgressionProofData

variable {B : Submodule ℤ Z} {extensionClass : Z →ₗ[ℤ] Rel}

/-- The denominator is exactly the kernel of the extension-class map. -/
theorem kernel_eq_boundary
    (P : TransgressionProofData B extensionClass) :
    LinearMap.ker extensionClass = B :=
  le_antisymm
    (TransgressionProofData.relative_zero_is_boundary P)
    (TransgressionProofData.boundaries_null P)

/-- Proposition 4.5 as a quotient equivalence. -/
def linearEquiv (P : TransgressionProofData B extensionClass) :
    (Z ⧸ B) ≃ₗ[ℤ] Rel :=
  transgression B extensionClass (kernel_eq_boundary P)
    P.representative_exists

/-- Formula (4.18) survives the quotient unchanged. -/
@[simp]
theorem linearEquiv_mkQ
    (P : TransgressionProofData B extensionClass) (z : Z) :
    P.linearEquiv (B.mkQ z) = extensionClass z :=
  transgression_mkQ B extensionClass (kernel_eq_boundary P)
    P.representative_exists z

end TransgressionProofData

end GeneralSphereT.Section4
