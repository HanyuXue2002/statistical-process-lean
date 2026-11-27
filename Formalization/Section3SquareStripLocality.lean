import Formalization.EllDistribution
import Formalization.IteratedLocality

set_option linter.style.header false

/-!
# Section 3: the square-strip replacement is a physical identity

This module proves the path-algebra heart of the simultaneous cone-operator
replacement.  If one elementary edge is replaced by a finite word of
elementary edges with the same physical endpoint, and visibility of every
letter implies visibility of the original edge, then applying the replacement
error to an elementary nonface cube lands in the full locality denominator.
-/

noncomputable section

namespace GeneralSphereT.PathAlgebra

universe uF uB

variable {ι G B : Type*}
variable [LinearOrder ι] [AddCommGroup G] [AddCommGroup B]
variable {Facet : Type uF}
variable {BAt : Facet → Type uB} [∀ ρ, AddCommGroup (BAt ρ)]
variable {d : Configuration ι G →+ B}

/-- A nonzero one-coordinate configuration, i.e. an elementary operator
label. -/
def IsElementaryLabel (r : Configuration ι G) : Prop :=
  ∃ (i : ι) (g : G), g ≠ 0 ∧ r = Finsupp.single i g

section AbstractFacetData

variable {facets : Facet → Set ι}
variable (L : FacetRestrictionData
  (CAt := fun ρ => Configuration (facets ρ) G)
  (BAt := BAt) (Facet := Facet) d)

omit [LinearOrder ι] in
/-- Replacing the first label by one whose visibility is contained in the
old label's visibility preserves the no-common-facet condition. -/
theorem noCommonFacetList_replace_head
    (t u : Configuration ι G) (rest : List (Configuration ι G))
    (hcommon : NoCommonFacetList L.primitiveRes (t :: rest))
    (hvisibility : ∀ ρ : Facet,
      L.primitiveRes ρ u ≠ 0 → L.primitiveRes ρ t ≠ 0) :
    NoCommonFacetList L.primitiveRes (u :: rest) := by
  rw [noCommonFacetList_iff] at hcommon ⊢
  intro ρ
  obtain ⟨s, hs, hzero⟩ := hcommon ρ
  simp only [List.mem_cons] at hs ⊢
  rcases hs with rfl | hs
  · refine ⟨u, Or.inl rfl, ?_⟩
    by_contra hu
    exact hvisibility ρ hu hzero
  · exact ⟨s, Or.inr hs, hzero⟩

omit [LinearOrder ι] in
/-- An iterated square with elementary active labels and the required
no-common-facet condition is literally one of the generators of the physical
identity denominator. -/
theorem iteratedPhysicalLocalitySquare_mem_physicalIdentityPaths_of_elementary
    {s t : Configuration ι G}
    (hs : IsElementaryLabel s) (ht : IsElementaryLabel t)
    (rs : List (Configuration ι G)) (a : B)
    (hcommon : NoCommonFacetList L.primitiveRes (s :: t :: rs)) :
    iteratedPhysicalLocalitySquare d s t rs a ∈
      physicalIdentityPaths L := by
  rcases hs with ⟨i, g, hg, rfl⟩
  rcases ht with ⟨j, h, hh, rfl⟩
  apply Submodule.subset_span
  exact ⟨i, g, j, h, rs, a, hg, hh, hcommon, rfl⟩

omit [LinearOrder ι] in
/-- Every square in the replacement word gives a denominator generator, and
the whole square strip therefore lies in the denominator. -/
theorem iteratedSquareStrip_mem_physicalIdentityPaths
    (t r : Configuration ι G) (word rs : List (Configuration ι G)) (a : B)
    (hr : IsElementaryLabel r)
    (hword : ∀ u ∈ word, IsElementaryLabel u)
    (hvisibility : ∀ u ∈ word, ∀ ρ : Facet,
      L.primitiveRes ρ u ≠ 0 → L.primitiveRes ρ t ≠ 0)
    (hcommon : NoCommonFacetList L.primitiveRes (t :: r :: rs)) :
    iteratedBaseDifference d rs (squareStrip d word r a) ∈
      physicalIdentityPaths L := by
  induction word generalizing a with
  | nil => simp [squareStrip]
  | cons u word ih =>
      simp only [squareStrip, map_add]
      apply Submodule.add_mem
      · change iteratedPhysicalLocalitySquare d u r rs a ∈
          physicalIdentityPaths L
        apply
          iteratedPhysicalLocalitySquare_mem_physicalIdentityPaths_of_elementary
            L (hword u (by simp)) hr rs a
        exact noCommonFacetList_replace_head L t u (r :: rs) hcommon
          (hvisibility u (by simp))
      · apply ih
        · intro w hw
          exact hword w (by simp [hw])
        · intro w hw ρ hwρ
          exact hvisibility w (by simp [hw]) ρ hwρ

omit [LinearOrder ι] in
/-- The elementary-cube form of the square-strip argument: the linearized
one-edge-minus-word error belongs to the physical identity denominator. -/
theorem ellDistribution_elementaryCube_mem_physicalIdentityPaths
    (t r : Configuration ι G) (word rs : List (Configuration ι G)) (a : B)
    (ht : IsElementaryLabel t) (hr : IsElementaryLabel r)
    (hword : ∀ u ∈ word, IsElementaryLabel u)
    (hendpoint : d (wordIncrement word) = d t)
    (hvisibility : ∀ u ∈ word, ∀ ρ : Facet,
      L.primitiveRes ρ u ≠ 0 → L.primitiveRes ρ t ≠ 0)
    (hcommon : NoCommonFacetList L.primitiveRes (t :: r :: rs)) :
    ellDistribution d t word
        (iteratedDistributionDifference ((r :: rs).map d)
          (Finsupp.single a 1)) ∈
      physicalIdentityPaths L := by
  rw [ellDistribution_elementaryCube d t word r rs a hendpoint, map_sub]
  exact Submodule.sub_mem _
    (iteratedSquareStrip_mem_physicalIdentityPaths
      L t r word rs a hr hword hvisibility hcommon)
    (iteratedPhysicalLocalitySquare_mem_physicalIdentityPaths_of_elementary
      L ht hr rs a hcommon)

end AbstractFacetData

end GeneralSphereT.PathAlgebra
