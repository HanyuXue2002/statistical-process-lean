import Formalization.ExplicitOrderedCellFilling
import Formalization.PrimitiveCellChains
import Formalization.CoordinateRestriction

set_option linter.style.header false

/-!
# Strict restriction naturality of the explicit ordered filling

The explicit two-chain from `ExplicitOrderedCellFilling` is itself natural,
not merely its path boundary.  The inherited order on a coordinate subtype is
essential: a source square indexed by `i < j` survives precisely when both
coordinates survive, and then becomes the target square with the same order.
-/

noncomputable section

open scoped BigOperators

namespace GeneralSphereT.PathAlgebra

variable {ι G : Type*} [LinearOrder ι] [AddCommGroup G]

/-- A square term whose two coordinates survive restriction becomes exactly
the corresponding square term on the coordinate subtype. -/
theorem restrictPrimitiveCellChain₂_orderedSquareCell_mem
    (S : Set ι) (c : Config ι G) {i j : ι}
    (hi : i ∈ S) (hj : j ∈ S) (g : G) :
    restrictPrimitiveCellChain₂ S (orderedSquareCell c i g j) =
      orderedSquareCell (coordinateRestriction S c) ⟨i, hi⟩ g ⟨j, hj⟩ := by
  classical
  by_cases hij : i < j
  · have hsub : (⟨i, hi⟩ : S) < ⟨j, hj⟩ := hij
    simp only [orderedSquareCell, hij, hsub, primitiveCellGenerator,
      dite_eq_left,
      restrictPrimitiveCellChain₂_single, one_smul,
      restrictPrimitiveCellGenerator, hi, hj,
      coordinateRestriction_apply]
    rw [coordinateRestriction_coordinatePrefix S c ⟨j, hj⟩]
  · have hsub : ¬(⟨i, hi⟩ : S) < ⟨j, hj⟩ := hij
    simp [orderedSquareCell, hij, hsub]

/-- A square term is deleted when its later coordinate is deleted. -/
theorem restrictPrimitiveCellChain₂_orderedSquareCell_not_mem_right
    (S : Set ι) (c : Config ι G) {i j : ι}
    (hj : j ∉ S) (g : G) :
    restrictPrimitiveCellChain₂ S (orderedSquareCell c i g j) = 0 := by
  classical
  by_cases hij : i < j
  · simp [orderedSquareCell, hij, primitiveCellGenerator,
      restrictPrimitiveCellGenerator, hj]
  · simp [orderedSquareCell, hij]

/-- If the distinguished coordinate is deleted, every square term is deleted
as well. -/
theorem restrictPrimitiveCellChain₂_orderedSquareCell_not_mem_left
    (S : Set ι) (c : Config ι G) {i : ι}
    (hi : i ∉ S) (g : G) (j : ι) :
    restrictPrimitiveCellChain₂ S (orderedSquareCell c i g j) = 0 := by
  classical
  by_cases hij : i < j
  · simp [orderedSquareCell, hij, primitiveCellGenerator,
      restrictPrimitiveCellGenerator, hi]
  · simp [orderedSquareCell, hij]

/-- When `i` survives, the explicitly selected primitive two-chain restricts
strictly to the selected chain for the restricted configuration. -/
theorem restrictPrimitiveCellChain₂_explicitOrderedCellFilling_mem
    (S : Set ι) (c : Config ι G) {i : ι} (hi : i ∈ S) (g : G) :
    restrictPrimitiveCellChain₂ S (explicitOrderedCellFilling c i g) =
      explicitOrderedCellFilling (coordinateRestriction S c) ⟨i, hi⟩ g := by
  classical
  have htriangle :
      restrictPrimitiveCellChain₂ S
          (primitiveCellGenerator (.sameCoordinateTriangle i (c i) g)
            (coordinatePrefix c i)) =
        primitiveCellGenerator
          (.sameCoordinateTriangle ⟨i, hi⟩
            ((coordinateRestriction S c) ⟨i, hi⟩) g)
          (coordinatePrefix (coordinateRestriction S c) ⟨i, hi⟩) := by
    simp only [primitiveCellGenerator, restrictPrimitiveCellChain₂_single,
      dite_eq_left, one_smul, restrictPrimitiveCellGenerator, hi,
      coordinateRestriction_apply]
    rw [coordinateRestriction_coordinatePrefix S c ⟨i, hi⟩]
  rw [explicitOrderedCellFilling, map_add, map_sum, htriangle]
  rw [explicitOrderedCellFilling, support_coordinateRestriction]
  congr 1
  let sourceTerm : ι → PrimitiveCellChain₂ S G := fun j =>
    restrictPrimitiveCellChain₂ S (orderedSquareCell c i g j)
  have htarget :
      (∑ j ∈ c.support.subtype (fun k => k ∈ S),
          orderedSquareCell (coordinateRestriction S c) ⟨i, hi⟩ g j) =
        ∑ j ∈ c.support.subtype (fun k => k ∈ S), sourceTerm j.1 := by
    apply Finset.sum_congr rfl
    intro j hjSupport
    exact (restrictPrimitiveCellChain₂_orderedSquareCell_mem
      S c hi j.2 g).symm
  rw [htarget]
  have hsubtype :
      (∑ j ∈ c.support.subtype (fun k => k ∈ S), sourceTerm j.1) =
        ∑ j ∈ c.support.filter (fun k => k ∈ S), sourceTerm j := by
    exact Finset.sum_subtype_eq_sum_filter
      (s := c.support) (p := fun k => k ∈ S) (f := sourceTerm)
  rw [hsubtype]
  have hfilter :
      (∑ j ∈ c.support.filter (fun k => k ∈ S), sourceTerm j) =
        ∑ j ∈ c.support, sourceTerm j := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro j hjSupport hjFilter
    have hj : j ∉ S := by
      intro hj
      exact hjFilter (Finset.mem_filter.mpr ⟨hjSupport, hj⟩)
    exact restrictPrimitiveCellChain₂_orderedSquareCell_not_mem_right
      S c hj g
  exact hfilter.symm

/-- When `i` is deleted, the entire explicitly selected filling is deleted. -/
theorem restrictPrimitiveCellChain₂_explicitOrderedCellFilling_not_mem
    (S : Set ι) (c : Config ι G) {i : ι} (hi : i ∉ S) (g : G) :
    restrictPrimitiveCellChain₂ S (explicitOrderedCellFilling c i g) = 0 := by
  classical
  rw [explicitOrderedCellFilling, map_add, map_sum]
  have htriangle :
      restrictPrimitiveCellChain₂ S
          (primitiveCellGenerator (.sameCoordinateTriangle i (c i) g)
            (coordinatePrefix c i)) = 0 := by
    simp [primitiveCellGenerator, restrictPrimitiveCellGenerator, hi]
  rw [htriangle, zero_add]
  apply Finset.sum_eq_zero
  intro j hj
  exact restrictPrimitiveCellChain₂_orderedSquareCell_not_mem_left
    S c hi g j

end GeneralSphereT.PathAlgebra
