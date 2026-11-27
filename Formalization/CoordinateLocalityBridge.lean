import Formalization.SameCoordinateIdentity
import Formalization.CoordinateRestriction

set_option linter.style.header false

/-!
# Coordinate support implies the abstract locality hypothesis

`SameCoordinateIdentity` states its three locality assumptions using the
abstract maps in `FacetRestrictionData`.  This module supplies the
coordinate-support bridge used in the paper: when primitive restriction to a
facet is literal coordinate deletion, one common geometric condition implies
all three assumptions, independently of the coefficients `g`, `h`, and
`g + h`.
-/

noncomputable section

namespace GeneralSphereT.PathAlgebra

universe uF uI uG uB

variable {ι : Type uI} {G : Type uG} [AddCommGroup G]

/-- Replace each coordinate/coefficient pair by its one-coordinate increment. -/
def oneCoordinateIncrements (steps : List (ι × G)) :
    List (Configuration ι G) :=
  steps.map fun p => Finsupp.single p.1 p.2

/--
A Lean-friendly form of the support condition used in the same-coordinate
triangle argument.

The first conjunct says that every listed coefficient is nonzero.  The second
says that no facet contains coordinate `i` together with all coordinates in
the list: facetwise, either `i` is absent or one listed coordinate is absent.
-/
def CoordinateLocalityFamily {Facet : Type uF}
    (facets : Facet → Set ι) (i : ι) (steps : List (ι × G)) : Prop :=
  (∀ p ∈ steps, p.2 ≠ 0) ∧
    ∀ ρ : Facet, i ∉ facets ρ ∨ ∃ p ∈ steps, p.1 ∉ facets ρ

theorem CoordinateLocalityFamily.coefficient_ne_zero
    {Facet : Type uF} {facets : Facet → Set ι} {i : ι}
    {steps : List (ι × G)}
    (h : CoordinateLocalityFamily facets i steps)
    {p : ι × G} (hp : p ∈ steps) :
    p.2 ≠ 0 :=
  h.1 p hp

/--
Literal coordinate restriction turns the geometric support condition into
`NoCommonFacetList`.  The conclusion actually holds for every coefficient
`ℓ`; the applications below only ask for it when `ℓ ≠ 0` because only
nonzero active increments occur among the physical locality generators.
-/
theorem CoordinateLocalityFamily.noCommonFacetList
    {Facet : Type uF} (facets : Facet → Set ι) (i : ι)
    (steps : List (ι × G))
    (h : CoordinateLocalityFamily facets i steps)
    (res : ∀ ρ : Facet,
      Configuration ι G →+ Configuration (facets ρ) G)
    (hres : ∀ ρ : Facet,
      res ρ = coordinateRestriction (facets ρ))
    (ℓ : G) :
    NoCommonFacetList res
      (Finsupp.single i ℓ :: oneCoordinateIncrements steps) := by
  rw [noCommonFacetList_iff]
  intro ρ
  rcases h.2 ρ with hi | ⟨p, hp, hpρ⟩
  · refine ⟨Finsupp.single i ℓ, List.mem_cons_self, ?_⟩
    rw [hres ρ]
    exact coordinateRestriction_single_not_mem (facets ρ) hi ℓ
  · refine ⟨Finsupp.single p.1 p.2, ?_, ?_⟩
    · apply List.mem_cons_of_mem
      exact List.mem_map.mpr ⟨p, hp, rfl⟩
    · rw [hres ρ]
      exact coordinateRestriction_single_not_mem (facets ρ) hpρ p.2

section SameCoordinateApplication

variable {B : Type uB} [AddCommGroup B]
variable {Facet : Type uF} (facets : Facet → Set ι)
variable {BAt : Facet → Type*} [∀ ρ, AddCommGroup (BAt ρ)]
variable {d : Configuration ι G →+ B}

variable (L : FacetRestrictionData
  (CAt := fun ρ => Configuration (facets ρ) G)
  (BAt := BAt) (Facet := Facet) d)

/--
Coordinate-support version of the same-coordinate triangle lemma.

The first listed step is the transverse increment `(j,β)` and `tail`
contains the remaining one-coordinate differences.  A single geometric
condition for `i :: j :: tail` supplies the locality hypotheses for the
`g + h`, `g`, and `h` square terms in equation (2.32).
-/
theorem
    iteratedBaseDifference_sameCoordinateTriangle_mem_physicalIdentityPaths_of_coordinateSupport
    (hprimitive : ∀ ρ : Facet,
      L.primitiveRes ρ = coordinateRestriction (facets ρ))
    (i j : ι) (hij : i ≠ j) (g h β : G)
    (tail : List (ι × G)) (a : B)
    (hlocal : CoordinateLocalityFamily facets i ((j, β) :: tail)) :
    iteratedBaseDifference d (oneCoordinateIncrements tail)
        (baseDifference (d (Finsupp.single j β))
          (triangle d (Finsupp.single i g) (Finsupp.single i h) a)) ∈
      physicalIdentityPaths L := by
  have hβ : β ≠ 0 :=
    hlocal.coefficient_ne_zero (p := (j, β)) (by simp)
  refine
    iteratedBaseDifference_sameCoordinateTriangle_mem_physicalIdentityPaths
      L i j hij g h β hβ (oneCoordinateIncrements tail) a ?_ ?_ ?_
  · intro _hgh
    simpa [oneCoordinateIncrements] using
      hlocal.noCommonFacetList facets i ((j, β) :: tail)
        L.primitiveRes hprimitive (g + h)
  · intro _hg
    simpa [oneCoordinateIncrements] using
      hlocal.noCommonFacetList facets i ((j, β) :: tail)
        L.primitiveRes hprimitive g
  · intro _hh
    simpa [oneCoordinateIncrements] using
      hlocal.noCommonFacetList facets i ((j, β) :: tail)
        L.primitiveRes hprimitive h

end SameCoordinateApplication

end GeneralSphereT.PathAlgebra
