import Formalization.CoordinateRestriction

set_option linter.style.header false

/-!
# Extension by zero along a coordinate subset

Restriction to a family of coordinates has a canonical section obtained by
putting zero on every omitted coordinate.  The closed-star correction in the
relative primitive argument uses exactly this elementary operation.
-/

noncomputable section

namespace GeneralSphereT.PathAlgebra

variable {ι G : Type*} [AddCommGroup G]

/-- Extend a finitely indexed configuration by zero outside `S`. -/
def coordinateExtension (S : Set ι) :
    Configuration S G →+ Configuration ι G :=
  Finsupp.mapDomain.addMonoidHom Subtype.val

@[simp]
theorem coordinateExtension_apply_mem (S : Set ι)
    (c : Configuration S G) {i : ι} (hi : i ∈ S) :
    coordinateExtension S c i = c ⟨i, hi⟩ := by
  change Finsupp.mapDomain Subtype.val c i = c ⟨i, hi⟩
  simpa using Finsupp.mapDomain_apply Subtype.val_injective c ⟨i, hi⟩

@[simp]
theorem coordinateExtension_apply_not_mem (S : Set ι)
    (c : Configuration S G) {i : ι} (hi : i ∉ S) :
    coordinateExtension S c i = 0 := by
  apply Finsupp.mapDomain_of_notMem_range
  rintro ⟨j, rfl⟩
  exact hi j.2

/-- Extension by zero is a strict right inverse to coordinate restriction. -/
@[simp]
theorem coordinateRestriction_coordinateExtension (S : Set ι)
    (c : Configuration S G) :
    coordinateRestriction S (coordinateExtension S c) = c := by
  ext i
  exact coordinateExtension_apply_mem S c i.2

end GeneralSphereT.PathAlgebra
