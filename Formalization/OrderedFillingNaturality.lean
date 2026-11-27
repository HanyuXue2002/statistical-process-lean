import Formalization.OrderedFilling

set_option linter.style.header false

/-!
# Restriction naturality of the ordered elementary-edge filling

The final comparison loop commutes strictly with coordinate restriction.  At
the level of the filling used in `OrderedFilling`, restriction sends every
primitive square or triangle boundary either to the corresponding cell
boundary on the coordinate subtype or to zero.  Consequently it preserves the
cell-boundary span, without choosing a separate type of two-chains.
-/

noncomputable section

namespace GeneralSphereT.PathAlgebra

variable {ι G : Type*} [LinearOrder ι] [AddCommGroup G]

/-- The final loop in `elementary_edge_ordered_loop_mem`, named so that its
naturality can be stated without repeating the expression. -/
def elementaryEdgeOrderedLoop (c : Config ι G) (i : ι) (g : G) :
    Path (Config ι G) (Config ι G) :=
  orderedPath c 0 + edge (Finsupp.single i g) c -
    orderedPath (c + Finsupp.single i g) 0

theorem elementaryEdgeOrderedLoop_mem (c : Config ι G) (i : ι) (g : G) :
    elementaryEdgeOrderedLoop c i g ∈
      primitiveCellBoundaries (ι := ι) (G := G) := by
  exact elementary_edge_ordered_loop_mem c i g

/-- If the distinguished coordinate survives restriction, the comparison
loop restricts to the comparison loop on the inherited coordinate subtype. -/
theorem mapPath_elementaryEdgeOrderedLoop_coordinateRestriction_mem
    (S : Set ι) (c : Config ι G) {i : ι} (hi : i ∈ S) (g : G) :
    mapPath (coordinateRestriction S) (coordinateRestriction S)
        (elementaryEdgeOrderedLoop c i g) =
      elementaryEdgeOrderedLoop (coordinateRestriction S c) ⟨i, hi⟩ g := by
  simp [elementaryEdgeOrderedLoop,
    mapPath_orderedPath_coordinateRestriction,
    coordinateRestriction_single_mem S hi]

/-- If the distinguished coordinate is deleted, the entire comparison loop
restricts to zero. -/
theorem mapPath_elementaryEdgeOrderedLoop_coordinateRestriction_not_mem
    (S : Set ι) (c : Config ι G) {i : ι} (hi : i ∉ S) (g : G) :
    mapPath (coordinateRestriction S) (coordinateRestriction S)
        (elementaryEdgeOrderedLoop c i g) = 0 := by
  simp [elementaryEdgeOrderedLoop,
    mapPath_orderedPath_coordinateRestriction,
    coordinateRestriction_single_not_mem S hi]

omit [LinearOrder ι] in
/-- Mapping both increments and base points by the same additive map sends a
primitive square to the corresponding square. -/
theorem mapPath_square_self {J : Type*} [AddCommGroup J]
    (f : Config ι G →+ J) (s t c : Config ι G) :
    mapPath f f
        (square (AddMonoidHom.id (Config ι G)) s t c) =
      square (AddMonoidHom.id J) (f s) (f t) (f c) := by
  simp [square]

omit [LinearOrder ι] in
/-- Mapping both increments and base points by the same additive map sends a
primitive triangle to the corresponding triangle. -/
theorem mapPath_triangle_self {J : Type*} [AddCommGroup J]
    (f : Config ι G →+ J) (g h c : Config ι G) :
    mapPath f f
        (triangle (AddMonoidHom.id (Config ι G)) g h c) =
      triangle (AddMonoidHom.id J) (f g) (f h) (f c) := by
  simp [triangle]

/-- A transverse square restricts to a transverse square or to zero. -/
theorem mapPath_coordinateRestriction_square_mem (S : Set ι)
    {i j : ι} (hij : i ≠ j) (g h : G) (c : Config ι G) :
    mapPath (coordinateRestriction S) (coordinateRestriction S)
        (square (AddMonoidHom.id (Config ι G))
          (Finsupp.single i g) (Finsupp.single j h) c) ∈
      primitiveCellBoundaries (ι := S) (G := G) := by
  rw [mapPath_square_self]
  by_cases hi : i ∈ S
  · by_cases hj : j ∈ S
    · rw [coordinateRestriction_single_mem S hi]
      rw [coordinateRestriction_single_mem S hj]
      apply square_mem_primitiveCellBoundaries
      intro heq
      exact hij (Subtype.ext_iff.mp heq)
    · rw [coordinateRestriction_single_not_mem S hj]
      simp
  · rw [coordinateRestriction_single_not_mem S hi]
    simp

/-- A one-coordinate triangle restricts to the corresponding triangle or to
zero. -/
theorem mapPath_coordinateRestriction_triangle_mem (S : Set ι)
    (i : ι) (g h : G) (c : Config ι G) :
    mapPath (coordinateRestriction S) (coordinateRestriction S)
        (triangle (AddMonoidHom.id (Config ι G))
          (Finsupp.single i g) (Finsupp.single i h) c) ∈
      primitiveCellBoundaries (ι := S) (G := G) := by
  rw [mapPath_triangle_self]
  by_cases hi : i ∈ S
  · simp only [coordinateRestriction_single_mem S hi]
    apply Submodule.subset_span
    exact Or.inr ⟨⟨i, hi⟩, g, h, coordinateRestriction S c, rfl⟩
  · rw [coordinateRestriction_single_not_mem S hi]
    simp

/-- Every primitive cell-boundary generator restricts into the target
cell-boundary span. -/
theorem mapPath_coordinateRestriction_cellGenerator_mem (S : Set ι)
    {p : Path (Config ι G) (Config ι G)}
    (hp : p ∈ primitiveCellBoundaryGenerators (ι := ι) (G := G)) :
    mapPath (coordinateRestriction S) (coordinateRestriction S) p ∈
      primitiveCellBoundaries (ι := S) (G := G) := by
  rcases hp with hp | hp
  · rcases hp with ⟨i, j, g, h, c, hij, rfl⟩
    exact mapPath_coordinateRestriction_square_mem S hij g h c
  · rcases hp with ⟨i, g, h, c, rfl⟩
    exact mapPath_coordinateRestriction_triangle_mem S i g h c

/-- Coordinate restriction sends the chosen primitive cell-boundary span to
the corresponding span on the coordinate subtype.  A deleted coordinate
makes its square or triangle degenerate, hence zero in `Path`. -/
theorem mapPath_coordinateRestriction_primitiveCellBoundaries_mem
    (S : Set ι) {p : Path (Config ι G) (Config ι G)}
    (hp : p ∈ primitiveCellBoundaries (ι := ι) (G := G)) :
    mapPath (coordinateRestriction S) (coordinateRestriction S) p ∈
      primitiveCellBoundaries (ι := S) (G := G) := by
  change p ∈ Submodule.span ℤ
    (primitiveCellBoundaryGenerators (ι := ι) (G := G)) at hp
  induction hp using Submodule.span_induction with
  | mem p hp => exact mapPath_coordinateRestriction_cellGenerator_mem S hp
  | zero => simp
  | add p q hp hq ihp ihq =>
      simpa using
        (primitiveCellBoundaries (ι := S) (G := G)).add_mem ihp ihq
  | smul n p hp ih =>
      simpa using
        (primitiveCellBoundaries (ι := S) (G := G)).smul_mem n ih

end GeneralSphereT.PathAlgebra
