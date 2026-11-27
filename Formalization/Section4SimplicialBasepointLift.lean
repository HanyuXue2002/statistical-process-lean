import Formalization.Section4BasedDegreeZero
import Formalization.Section4FiberwiseExtension
import Formalization.SimplicialDegreeZero

set_option linter.style.header false
set_option linter.style.haveILetI false

/-!
# Section 4: the simplicial basepoint lift

For cochain degree zero, evaluation on the singleton facet at a chosen vertex
has a section: extend the one local value to the global constant zero-cochain.
The constant cochain has zero coboundary, so the free reduced-distribution
extension sends local primitive relations to global primitive relations.

In every positive cochain degree the singleton facet has no simplices.  Its
local configuration group is therefore a singleton, and so is its reduced
primitive relation group.  These two observations supply the concrete
basepoint-lift input required by the abstract based degree-zero row.
-/

noncomputable section

namespace GeneralSphereT.SimplicialCochain

open GeneralSphereT.PathAlgebra
open GeneralSphereT.PathAlgebra.FacetRestrictionData

variable {V G : Type*} [LinearOrder V] [Fintype V] [AddCommGroup G]
variable (K : AbstractSimplicialComplex V) (b : V)

/-- The chosen vertex as a degree-zero simplex. -/
def basepointSimplex : Simplex K 0 :=
  ⟨{b}, K.singleton_mem b, by simp⟩

/-- The chosen vertex as a facet in the all-simplex facet presentation. -/
def basepointFacet : NonemptySimplex K :=
  ⟨{b}, K.singleton_mem b⟩

/-- The unique degree-zero face of the singleton basepoint facet. -/
def basepointLocalFace : facesIn K 0 (basepointFacet K b) :=
  ⟨basepointSimplex K b, Finset.Subset.rfl⟩

omit [LinearOrder V] [Fintype V] in
/-- Every degree-zero face of the singleton facet is the chosen vertex. -/
theorem facesIn_zero_basepoint_eq
    (η : facesIn K 0 (basepointFacet K b)) :
    η = basepointLocalFace K b := by
  apply Subtype.ext
  apply Subtype.ext
  change η.1.1 = {b}
  apply Finset.eq_of_subset_of_card_le η.2
  simpa only [basepointFacet, Finset.card_singleton, Nat.zero_add] using
    η.1.2.2.ge

/-- Read the unique value of a local zero-cochain on the basepoint facet. -/
def basepointLocalValue
    (c : Configuration (facesIn K 0 (basepointFacet K b)) G) : G :=
  c (basepointLocalFace K b)

/-- Extend a local zero-cochain on the singleton facet to the global constant
zero-cochain with the same value. -/
def basepointConstantExtension
    (c : Configuration (facesIn K 0 (basepointFacet K b)) G) :
    Cochain K 0 G :=
  constantCochain K (basepointLocalValue K b c)

omit [LinearOrder V] in
/-- Restriction of the global constant extension is the original local
zero-cochain. -/
theorem restrict_basepointConstantExtension
    (c : Configuration (facesIn K 0 (basepointFacet K b)) G) :
    restrictCochain K 0 (basepointFacet K b)
        (basepointConstantExtension K b c) = c := by
  ext η
  rw [restrictCochain_apply, basepointConstantExtension,
    constantCochain_apply, basepointLocalValue,
    facesIn_zero_basepoint_eq K b η]

/-- The constant extension is a fiberwise cochain lift from the singleton
facet to the whole complex. -/
def basepointConstantFiberwiseLift :
    FiberwiseCochainLift
      ((facetRestrictionData (G := G) K 0).localD (basepointFacet K b))
      (coboundaryToRange (G := G) K 0)
      ((facetRestrictionData (G := G) K 0).primitiveRes
        (basepointFacet K b)) where
  lift := basepointConstantExtension K b
  physicalLift := fun _ => 0
  res_lift c := by
    exact restrict_basepointConstantExtension K b c
  d_lift c := by
    apply Subtype.ext
    change coboundary K 0 (basepointConstantExtension K b c) = 0
    simp [basepointConstantExtension]

/-- In cochain degree zero (`q = 1` in the paper), global constant extension
gives the required section on primitive relation distributions. -/
def basepointRelationLiftZero :
    BasepointRelationLiftData
      (facetRestrictionData (G := G) K 0) (basepointFacet K b) where
  constantLift := (basepointConstantFiberwiseLift K b).relationSection
  eval_constantLift := by
    apply LinearMap.ext
    intro u
    apply Subtype.ext
    change
      mapRedDist
          ((facetRestrictionData (G := G) K 0).primitiveRes
            (basepointFacet K b))
          (((basepointConstantFiberwiseLift K b).relationSection u).1) =
        u.1
    exact
      (basepointConstantFiberwiseLift K b).mapRedDist_relationSection u

/-- On reduced distributions, the degree-zero relation lift is pushforward
along global constant extension. -/
@[simp]
theorem basepointRelationLiftZero_coe
    (u : BasepointPrimitiveKernel
      (facetRestrictionData (G := G) K 0) (basepointFacet K b)) :
    (((basepointRelationLiftZero K b).constantLift u :
        Rprim (d := coboundaryToRange (G := G) K 0)) :
      RedDist (Cochain K 0 G)) =
      mapRedDistFn (basepointConstantExtension K b) u.1 :=
  rfl

/-- Basepoint evaluation of the degree-zero constant relation lift is the
original local primitive relation. -/
@[simp]
theorem evalRprim_basepointRelationLiftZero
    (u : BasepointPrimitiveKernel
      (facetRestrictionData (G := G) K 0) (basepointFacet K b)) :
    evalRprim (facetRestrictionData (G := G) K 0)
        (basepointFacet K b)
        ((basepointRelationLiftZero K b).constantLift u) = u := by
  have h := LinearMap.congr_fun
    (basepointRelationLiftZero K b).eval_constantLift u
  simpa using h

omit [LinearOrder V] [Fintype V] in
/-- A singleton vertex facet has no positive-dimensional faces. -/
theorem facesIn_succ_basepoint_isEmpty (m : ℕ) :
    IsEmpty (facesIn K (m + 1) (basepointFacet K b)) :=
  ⟨fun η => by
    have hle : η.1.1.card ≤ (basepointFacet K b).1.card :=
      Finset.card_le_card η.2
    have hcard : η.1.1.card = (m + 1) + 1 := η.1.2.2
    simp only [basepointFacet, Finset.card_singleton] at hle
    omega⟩

/-- The augmentation-zero distribution group on a one-point type is zero. -/
theorem redDist_subsingleton_of_unique (X : Type*) [Unique X] :
    Subsingleton (RedDist X) := by
  constructor
  intro u v
  have hzero : ∀ z : RedDist X, z = 0 := by
    intro z
    apply Subtype.ext
    rw [Finsupp.unique_single z.1]
    have hz : z.1 default = 0 := by
      have haug : augmentation X z.1 = 0 := LinearMap.mem_ker.mp z.2
      rw [Finsupp.unique_single z.1, augmentation_single] at haug
      exact haug
    simp [hz]
  rw [hzero u, hzero v]

/-- In every positive cochain degree, the basepoint local primitive kernel is
zero: there are no positive-dimensional simplices in a singleton facet. -/
theorem basepointPrimitiveKernel_succ_subsingleton (m : ℕ) :
    Subsingleton
      (BasepointPrimitiveKernel
        (facetRestrictionData (G := G) K (m + 1))
        (basepointFacet K b)) := by
  letI : IsEmpty (facesIn K (m + 1) (basepointFacet K b)) :=
    facesIn_succ_basepoint_isEmpty K b m
  letI : Unique
      (Configuration (facesIn K (m + 1) (basepointFacet K b)) G) :=
    inferInstance
  letI : Subsingleton
      (RedDist
        (Configuration (facesIn K (m + 1) (basepointFacet K b)) G)) :=
    redDist_subsingleton_of_unique _
  exact inferInstance

/-- The positive-degree basepoint lift is the unique map out of the zero
local primitive kernel. -/
def basepointRelationLiftSucc (m : ℕ) :
    BasepointRelationLiftData
      (facetRestrictionData (G := G) K (m + 1))
      (basepointFacet K b) := by
  letI : Subsingleton
      (BasepointPrimitiveKernel
        (facetRestrictionData (G := G) K (m + 1))
        (basepointFacet K b)) :=
    basepointPrimitiveKernel_succ_subsingleton K b m
  exact BasepointRelationLiftData.ofSubsingleton
    (facetRestrictionData (G := G) K (m + 1)) (basepointFacet K b)

/-- Concrete basepoint lift data in every cochain degree.  Degree zero uses
global constants; positive degrees use the trivial local kernel. -/
def basepointRelationLift (n : ℕ) :
    BasepointRelationLiftData
      (facetRestrictionData (G := G) K n) (basepointFacet K b) := by
  cases n with
  | zero => exact basepointRelationLiftZero K b
  | succ m => exact basepointRelationLiftSucc K b m

/-! ## The concrete based row -/

/-- The ambient vertex order supplies the coordinate order used by the cube
presentation of the physical identity subgroup. -/
local instance basepointSimplexColexOrder (n : ℕ) :
    LinearOrder (Simplex K n) :=
  LinearOrder.lift'
    (fun η : Simplex K n => toColex η.1)
    ((toColex : Finset V ≃ Colex (Finset V)).injective.comp
      Subtype.val_injective)

/-- The concrete obstruction arrow in cochain degree `n`. -/
def simplicialObstruction (n : ℕ) :
    StrictFSections (facetRestrictionData (G := G) K n) →ₗ[ℤ]
      Tau (fun σ : NonemptySimplex K => facesIn K n σ)
        (facetRestrictionData (G := G) K n) :=
  obstruction
    (fun σ : NonemptySimplex K => facesIn K n σ)
    (facetRestrictionData (G := G) K n)
    (simplicialMapLocallyZero_eq_physicalNonfaceCubeSpan
      (G := G) K n)

/-- The abstract based-row package with the concrete simplicial basepoint
lift inserted. -/
def simplicialBasepointRowData (n : ℕ) :
    GeneralSphereT.Section4.BasedRowData
      (BasepointPrimitiveKernel
        (facetRestrictionData (G := G) K n) (basepointFacet K b))
      (zprimToRprim (facetRestrictionData (G := G) K n))
      (restrictionClass (facetRestrictionData (G := G) K n)) :=
  (basepointRelationLift K b n).toBasedRowData

/-- The concrete obstruction restricted to strict sections whose value at the
chosen vertex facet is zero. -/
def simplicialBasedObstruction (n : ℕ) :
    LinearMap.ker
        (simplicialBasepointRowData (G := G) K b n).evalM →ₗ[ℤ]
      Tau (fun σ : NonemptySimplex K => facesIn K n σ)
        (facetRestrictionData (G := G) K n) :=
  GeneralSphereT.Section4.BasedRowData.basedObstruction
    (Q := Tau (fun σ : NonemptySimplex K => facesIn K n σ)
      (facetRestrictionData (G := G) K n))
    (simplicialBasepointRowData (G := G) K b n)
    (simplicialObstruction (G := G) K n)

/-- The complete concrete based degree-zero row for finite ordered simplicial
cochains.  No extra image, surjectivity, or basepoint-lift hypothesis remains. -/
theorem simplicialBasedDegreeZeroRow (n : ℕ) :
    Function.Injective
        (simplicialBasepointRowData (G := G) K b n).cyclesToBasedRelations ∧
      Function.Exact
          (simplicialBasepointRowData
            (G := G) K b n).cyclesToBasedRelations
          (simplicialBasepointRowData (G := G) K b n).basedRestriction ∧
      Function.Exact
          (simplicialBasepointRowData (G := G) K b n).basedRestriction
          (simplicialBasedObstruction (G := G) K b n) ∧
      Function.Surjective
        (simplicialBasedObstruction (G := G) K b n) := by
  exact basedDegreeZeroRow
    (fun σ : NonemptySimplex K => facesIn K n σ)
    (facetRestrictionData (G := G) K n)
    (basepointFacet K b)
    (basepointRelationLift K b n)
    (simplicialMapLocallyZero_eq_physicalNonfaceCubeSpan
      (G := G) K n)
    (simplicialMapRedDist_surjective (G := G) K n)

end GeneralSphereT.SimplicialCochain
