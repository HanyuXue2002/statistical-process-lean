import Formalization.Section4BasedRow
import Formalization.Section4DegreeZeroRow

set_option linter.style.header false

/-!
# Section 4: the based algebraic degree-zero row

This file connects the concrete degree-zero restriction row with the abstract
based-row argument.  Fixing one facet `b`, evaluation takes values in the
local primitive kernel for `b`.  Evaluation on compatible representatives
kills the locally-zero denominator and hence descends to `StrictFSections`.

The passage to a surjective based obstruction requires precisely one extra
input: a linear right inverse to evaluation on primitive relations.  This is
packaged in `BasepointRelationLiftData`.  In the simplicial application it is
the global-constant lift for `q = 1`; for `q > 1` the local evaluation group is
zero and the data is automatic.
-/

noncomputable section

namespace GeneralSphereT.PathAlgebra

universe uF uC uB

namespace FacetRestrictionData

section Evaluation

variable {C B : Type*} [AddCommGroup C] [AddCommGroup B]
variable {Facet : Type uF}
variable {CAt : Facet → Type uC} {BAt : Facet → Type uB}
variable [∀ ρ, AddCommGroup (CAt ρ)] [∀ ρ, AddCommGroup (BAt ρ)]
variable {d : C →+ B}

variable (L : FacetRestrictionData
  (CAt := CAt) (BAt := BAt) (Facet := Facet) d)
variable (b : Facet)

/-- The value group at the chosen basepoint facet: the kernel of the local
physical coboundary on reduced primitive distributions. -/
abbrev BasepointPrimitiveKernel := Rprim (d := L.localD b)

/-- Evaluation of a global primitive relation at the chosen facet. -/
def evalRprim :
    Rprim (d := d) →ₗ[ℤ] BasepointPrimitiveKernel L b :=
  LinearMap.codRestrict (BasepointPrimitiveKernel L b)
    ((L.restrictRedDist b).comp (Rprim (d := d)).subtype) fun r => by
      change
        mapRedDist (L.localD b)
          (L.restrictRedDist b (r : RedDist C)) = 0
      calc
        mapRedDist (L.localD b) (L.restrictRedDist b (r : RedDist C)) =
            L.restrictPhysicalRedDist b
              (mapRedDist d (r : RedDist C)) :=
          (LinearMap.congr_fun
            (L.restrictPhysicalRedDist_mapRedDist b)
            (r : RedDist C)).symm
        _ = 0 := by rw [LinearMap.mem_ker.mp r.property, map_zero]

@[simp]
theorem evalRprim_coe (r : Rprim (d := d)) :
    ((evalRprim L b r : BasepointPrimitiveKernel L b) :
      RedDist (CAt b)) = L.restrictRedDist b (r : RedDist C) :=
  rfl

/-- Evaluation of an `F`-compatible representative at the chosen facet.  Its
value lies in the local primitive kernel because the physical pushforward is
locally zero. -/
def evalFCompatible :
    fCompatibleRedDist L →ₗ[ℤ] BasepointPrimitiveKernel L b :=
  LinearMap.codRestrict (BasepointPrimitiveKernel L b)
    ((L.restrictRedDist b).comp (fCompatibleRedDist L).subtype) fun u => by
      change
        mapRedDist (L.localD b)
          (L.restrictRedDist b (u : RedDist C)) = 0
      have hphysical :
          L.restrictPhysicalRedDist b
            (mapRedDist d (u : RedDist C)) = 0 := by
        have hb :=
          (Submodule.mem_iInf (fun ρ : Facet =>
            LinearMap.ker (L.restrictPhysicalRedDist ρ))).1 u.property b
        exact LinearMap.mem_ker.mp hb
      calc
        mapRedDist (L.localD b) (L.restrictRedDist b (u : RedDist C)) =
            L.restrictPhysicalRedDist b
              (mapRedDist d (u : RedDist C)) :=
          (LinearMap.congr_fun
            (L.restrictPhysicalRedDist_mapRedDist b)
            (u : RedDist C)).symm
        _ = 0 := hphysical

@[simp]
theorem evalFCompatible_coe (u : fCompatibleRedDist L) :
    ((evalFCompatible L b u : BasepointPrimitiveKernel L b) :
      RedDist (CAt b)) = L.restrictRedDist b (u : RedDist C) :=
  rfl

/-- A representative which is zero on every facet has zero evaluation at the
chosen facet. -/
theorem locallyZeroInFCompatible_le_ker_evalFCompatible :
    locallyZeroInFCompatible L ≤ LinearMap.ker (evalFCompatible L b) := by
  intro u hu
  rw [LinearMap.mem_ker]
  apply Subtype.ext
  change L.restrictRedDist b (u : RedDist C) = 0
  have hb :=
    (Submodule.mem_iInf (fun ρ : Facet =>
      LinearMap.ker (L.restrictRedDist ρ))).1 hu b
  exact LinearMap.mem_ker.mp hb

/-- Basepoint evaluation descended to strict compatible `F`-sections. -/
def evalStrictFSections :
    StrictFSections L →ₗ[ℤ] BasepointPrimitiveKernel L b :=
  (locallyZeroInFCompatible L).liftQ (evalFCompatible L b)
    (locallyZeroInFCompatible_le_ker_evalFCompatible L b)

@[simp]
theorem evalStrictFSections_mkQ (u : fCompatibleRedDist L) :
    evalStrictFSections L b ((locallyZeroInFCompatible L).mkQ u) =
      evalFCompatible L b u := by
  rfl

/-- Restriction and basepoint evaluation commute. -/
theorem evalStrictFSections_comp_restrictionClass :
    (evalStrictFSections L b).comp (restrictionClass L) = evalRprim L b := by
  apply LinearMap.ext
  intro r
  apply Subtype.ext
  rfl

/-- Primitive cycles have zero evaluation at every facet, in particular at
the chosen basepoint facet. -/
theorem evalRprim_comp_zprimToRprim :
    (evalRprim L b).comp (zprimToRprim L) = 0 := by
  apply LinearMap.ext
  intro z
  apply Subtype.ext
  change L.restrictRedDist b (z : RedDist C) = 0
  have hb :=
    (Submodule.mem_iInf (fun ρ : Facet =>
      LinearMap.ker (L.restrictRedDist ρ))).1 z.property.2 b
  exact LinearMap.mem_ker.mp hb

/-- Minimal extra input for passage to based objects: local values in the
basepoint primitive kernel have a linear lift to global primitive relations,
and evaluation of the lift is the original local value. -/
structure BasepointRelationLiftData where
  constantLift : BasepointPrimitiveKernel L b →ₗ[ℤ] Rprim (d := d)
  eval_constantLift :
    (evalRprim L b).comp constantLift = LinearMap.id

namespace BasepointRelationLiftData

variable (A : BasepointRelationLiftData L b)

/-- If the local primitive kernel is trivial, the basepoint lift data is
automatic.  This is the algebraic form used in the higher-degree case. -/
def ofSubsingleton [Subsingleton (BasepointPrimitiveKernel L b)] :
    BasepointRelationLiftData L b where
  constantLift := 0
  eval_constantLift := by
    apply LinearMap.ext
    intro a
    exact Subsingleton.elim _ _

/-- The concrete evaluation and lift data as the abstract `BasedRowData`
consumed by `Section4BasedRow`. -/
def toBasedRowData :
    GeneralSphereT.Section4.BasedRowData
      (BasepointPrimitiveKernel L b)
      (zprimToRprim L) (restrictionClass L) where
  evalR := evalRprim L b
  evalM := evalStrictFSections L b
  eval_restriction := evalStrictFSections_comp_restrictionClass L b
  cycles_based := evalRprim_comp_zprimToRprim L b
  constantLift := A.constantLift
  eval_constantLift := A.eval_constantLift

/-- The left arrow in the based degree-zero row remains injective. -/
theorem basedCyclesToRelations_injective :
    Function.Injective A.toBasedRowData.cyclesToBasedRelations :=
  A.toBasedRowData.cyclesToBasedRelations_injective
    (zprimToRprim_injective L)

/-- Exactness at based primitive relations. -/
theorem exact_basedCyclesToRelations_basedRestriction :
    Function.Exact A.toBasedRowData.cyclesToBasedRelations
      A.toBasedRowData.basedRestriction :=
  A.toBasedRowData.exact_cyclesToBasedRelations_basedRestriction
    (exact_zprimToRprim_restrictionClass L)

end BasepointRelationLiftData

end Evaluation

section BasedObstruction

variable {ι G : Type*} [LinearOrder ι] [AddCommGroup G]
variable {B : Type uB} [AddCommGroup B]
variable {Facet : Type uF} (facets : Facet → Set ι)
variable {BAt : Facet → Type uC} [∀ ρ, AddCommGroup (BAt ρ)]
variable {d : Configuration ι G →+ B}

variable (L : FacetRestrictionData
  (CAt := fun ρ => Configuration (facets ρ) G)
  (BAt := BAt) (Facet := Facet) d)
variable (b : Facet)
variable (A : BasepointRelationLiftData L b)

omit [LinearOrder ι] in
/-- Exactness at based strict sections for the physical obstruction map. -/
theorem exact_basedRestriction_basedObstruction
    (himage :
      Submodule.map (mapRedDist d) (locallyZeroRedDist L) =
        physicalNonfaceCubeSpan facets d) :
    Function.Exact A.toBasedRowData.basedRestriction
      (A.toBasedRowData.basedObstruction (obstruction facets L himage)) :=
  A.toBasedRowData.exact_basedRestriction_basedObstruction
    (obstruction facets L himage)
    (exact_restrictionClass_obstruction facets L himage)

omit [LinearOrder ι] in
/-- Every `Tau` class has a based strict-section representative. -/
theorem basedObstruction_surjective
    (himage :
      Submodule.map (mapRedDist d) (locallyZeroRedDist L) =
        physicalNonfaceCubeSpan facets d)
    (hsurj : Function.Surjective (mapRedDist d)) :
    Function.Surjective
      (A.toBasedRowData.basedObstruction (obstruction facets L himage)) :=
  A.toBasedRowData.basedObstruction_surjective
    (obstruction facets L himage)
    (exact_restrictionClass_obstruction facets L himage)
    (obstruction_surjective facets L himage hsurj)

omit [LinearOrder ι] in
/-- The complete algebraic based degree-zero row, collected in one theorem. -/
theorem basedDegreeZeroRow
    (himage :
      Submodule.map (mapRedDist d) (locallyZeroRedDist L) =
        physicalNonfaceCubeSpan facets d)
    (hsurj : Function.Surjective (mapRedDist d)) :
    Function.Injective A.toBasedRowData.cyclesToBasedRelations ∧
      Function.Exact A.toBasedRowData.cyclesToBasedRelations
        A.toBasedRowData.basedRestriction ∧
      Function.Exact A.toBasedRowData.basedRestriction
        (A.toBasedRowData.basedObstruction (obstruction facets L himage)) ∧
      Function.Surjective
        (A.toBasedRowData.basedObstruction (obstruction facets L himage)) := by
  exact ⟨A.basedCyclesToRelations_injective,
    A.exact_basedCyclesToRelations_basedRestriction,
    exact_basedRestriction_basedObstruction facets L b A himage,
    basedObstruction_surjective facets L b A himage hsurj⟩

end BasedObstruction

end FacetRestrictionData

end GeneralSphereT.PathAlgebra
