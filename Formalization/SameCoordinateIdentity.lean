import Formalization.IteratedLocality

set_option linter.style.header false

/-!
# The same-coordinate triangle calculation

This file isolates the algebraic use of equation (2.32) in the reverse
inclusion of Lemma (2.26).  It proves both the literal three-square identity and
the resulting membership in the full physical locality denominator.

At the level of the abstract `FacetRestrictionData` used here, restrictions are
not required to depend only on coordinate support.  The final theorem therefore
assumes the three `NoCommonFacetList` statements needed by its three square
terms.  For the simplicial coordinate restrictions in the paper, all three
follow from the stated support condition: no facet contains coordinate `i`
together with the support of the chosen cube.
-/

noncomputable section

namespace GeneralSphereT.PathAlgebra

universe uF uC uB

variable {ι G B : Type*}
variable [LinearOrder ι] [AddCommGroup G] [AddCommGroup B]

omit [LinearOrder ι] in
/--
Equation (2.32), with zero increments interpreted by the path quotient.  The
right side is written as three actual mixed squares; its third base point is
the translation of `a` by `d (single i g)`.
-/
theorem baseDifference_sameCoordinateTriangle
    (d : Configuration ι G →+ B)
    (i j : ι) (_hij : i ≠ j) (g h β : G) (_hβ : β ≠ 0) (a : B) :
    baseDifference (d (Finsupp.single j β))
        (triangle d (Finsupp.single i g) (Finsupp.single i h) a) =
      square d (Finsupp.single i (g + h)) (Finsupp.single j β) a -
        square d (Finsupp.single i g) (Finsupp.single j β) a -
        square d (Finsupp.single i h) (Finsupp.single j β)
          (a + d (Finsupp.single i g)) := by
  change
    baseTranslation (d (Finsupp.single j β))
          (triangle d (Finsupp.single i g) (Finsupp.single i h) a) -
        triangle d (Finsupp.single i g) (Finsupp.single i h) a = _
  rw [translate_triangle_sub_triangle]
  rw [baseTranslation_square]
  simp only [Finsupp.single_add]

section LocalityMembership

variable {Facet : Type uF}
variable {CAt : Facet → Type uC} {BAt : Facet → Type uB}
variable [∀ ρ, AddCommGroup (CAt ρ)] [∀ ρ, AddCommGroup (BAt ρ)]
variable {d : Configuration ι G →+ B}

variable (L : FacetRestrictionData
  (CAt := CAt) (BAt := BAt) (Facet := Facet) d)

omit [LinearOrder ι] in
/--
An iterated mixed square belongs to `physicalIdentityPaths`.  If its
same-coordinate coefficient is zero, the square itself vanishes, so no
nonzero-label generator is needed.
-/
theorem iteratedMixedSquare_mem_physicalIdentityPaths
    (i j : ι) (_hij : i ≠ j) (ℓ β : G) (hβ : β ≠ 0)
    (rs : List (Configuration ι G)) (a : B)
    (hlocal : ℓ ≠ 0 → NoCommonFacetList L.primitiveRes
      (Finsupp.single i ℓ :: Finsupp.single j β :: rs)) :
    iteratedPhysicalLocalitySquare d
        (Finsupp.single i ℓ) (Finsupp.single j β) rs a ∈
      physicalIdentityPaths L := by
  by_cases hℓ : ℓ = 0
  · subst ℓ
    simp [iteratedPhysicalLocalitySquare, physicalLocalitySquare]
  · apply Submodule.subset_span
    exact ⟨i, ℓ, j, β, rs, a, hℓ, hβ, hlocal hℓ, rfl⟩

omit [LinearOrder ι] in
/--
The key locality consequence of (2.32).  After choosing a transverse nonzero
coefficient `β`, applying all remaining finite differences to a
same-coordinate triangle difference produces an element of the complete
physical denominator.

The three locality hypotheses are deliberately explicit.  The paper derives
them simultaneously from its stronger geometric fact that no facet contains
coordinate `i` together with every coordinate in the cube support; that
support-only property is not part of abstract `FacetRestrictionData`.
-/
theorem iteratedBaseDifference_sameCoordinateTriangle_mem_physicalIdentityPaths
    (i j : ι) (hij : i ≠ j) (g h β : G) (hβ : β ≠ 0)
    (rs : List (Configuration ι G)) (a : B)
    (hsum : g + h ≠ 0 → NoCommonFacetList L.primitiveRes
      (Finsupp.single i (g + h) :: Finsupp.single j β :: rs))
    (hg : g ≠ 0 → NoCommonFacetList L.primitiveRes
      (Finsupp.single i g :: Finsupp.single j β :: rs))
    (hh : h ≠ 0 → NoCommonFacetList L.primitiveRes
      (Finsupp.single i h :: Finsupp.single j β :: rs)) :
    iteratedBaseDifference d rs
        (baseDifference (d (Finsupp.single j β))
          (triangle d (Finsupp.single i g) (Finsupp.single i h) a)) ∈
      physicalIdentityPaths L := by
  rw [baseDifference_sameCoordinateTriangle d i j hij g h β hβ a]
  simp only [map_sub]
  apply Submodule.sub_mem
  · apply Submodule.sub_mem
    · exact iteratedMixedSquare_mem_physicalIdentityPaths
        L i j hij (g + h) β hβ rs a hsum
    · exact iteratedMixedSquare_mem_physicalIdentityPaths
        L i j hij g β hβ rs a hg
  · exact iteratedMixedSquare_mem_physicalIdentityPaths
      L i j hij h β hβ rs (a + d (Finsupp.single i g)) hh

end LocalityMembership

end GeneralSphereT.PathAlgebra
