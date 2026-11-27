import Formalization.SimplicialRelativePrimitive
import Formalization.SimplicialDegreeZero

set_option linter.style.header false

/-!
# Degree-zero relative primitive normalization

In degree zero, the closed-star cone identity has the usual augmentation
term.  We remove it globally by subtracting the constant cochain whose value
is the chosen primitive at the apex.  This does not change the coboundary and
makes the closed-star restriction exactly the cone homotopy of the physical
coboundary.
-/

noncomputable section

namespace GeneralSphereT.SimplicialCochain

variable {V G : Type*} [LinearOrder V] [Fintype V] [AddCommGroup G]
variable (K : AbstractSimplicialComplex V)

/-- Restricting a global constant zero-cochain gives the corresponding
constant zero-cochain on every closed star. -/
@[simp]
theorem restrictClosedStar_constantCochain
    (η : {s : Finset V // s ∈ K}) (g : G) :
    restrictClosedStar K η 0 (constantCochain K g) =
      closedStarConstant K η g := by
  ext τ
  simp

/-- The degree-zero primitive normalized to vanish at the selected apex. -/
def normalizedPrimitiveZero (η : Simplex K 0)
    (a : CoboundaryGroup (G := G) K 0) : Cochain K 0 G :=
  let c := chosenPrimitive K 0 a
  let η' := forgetDimension K η
  let v := simplexApex K η
  c - constantCochain K
    (closedStarAugmentation K η' v (simplexApex_mem K η)
      (restrictClosedStar K η' 0 c))

/-- Degree-zero normalization does not change the global coboundary. -/
@[simp]
theorem coboundary_normalizedPrimitiveZero (η : Simplex K 0)
    (a : CoboundaryGroup (G := G) K 0) :
    coboundary K 0 (normalizedPrimitiveZero K η a) = a.1 := by
  simp [normalizedPrimitiveZero]

/-- On the closed star of the active vertex, the normalized degree-zero
primitive is exactly the cone homotopy applied to the restricted physical
coboundary. -/
theorem restrictClosedStar_normalizedPrimitiveZero (η : Simplex K 0)
    (a : CoboundaryGroup (G := G) K 0) :
    restrictClosedStar K (forgetDimension K η) 0
        (normalizedPrimitiveZero K η a) =
      coneHomotopy K (forgetDimension K η) (simplexApex K η)
        (simplexApex_mem K η) 0
        (restrictClosedStar K (forgetDimension K η) 1 a.1) := by
  let c := chosenPrimitive K 0 a
  let η' := forgetDimension K η
  let v := simplexApex K η
  have hcontract := closedStar_contraction_zero
    (G := G) K η' v (simplexApex_mem K η)
      (restrictClosedStar K η' 0 c)
  have hd :
      closedStarCoboundary K η' 0 (restrictClosedStar K η' 0 c) =
        restrictClosedStar K η' 1 a.1 := by
    calc
      _ = restrictClosedStar K η' 1 (coboundary K 0 c) := by
        simpa only [LinearMap.comp_apply] using
          (LinearMap.congr_fun
            (restrictClosedStar_coboundary (G := G) K η' 0) c).symm
      _ = restrictClosedStar K η' 1 a.1 := by simp [c]
  change restrictClosedStar K η' 0
      (c - constantCochain K
        (closedStarAugmentation K η' v (simplexApex_mem K η)
          (restrictClosedStar K η' 0 c))) = _
  rw [map_sub, restrictClosedStar_constantCochain, ← hd]
  exact hcontract.symm

end GeneralSphereT.SimplicialCochain
