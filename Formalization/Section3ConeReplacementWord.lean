import Formalization.Section3ConeOperatorReplacement
import Formalization.Section3SquareStripLocality
import Mathlib.Combinatorics.Colex

set_option linter.style.header false

/-!
# Section 3: the bottom cochain as an elementary replacement word

The cochain `coneBottomReplacement t` is converted into the ordered list of
its nonzero coordinate increments.  This is the word consumed by the
square-strip argument: all letters are elementary, their sum is the bottom
cochain, and a facet which sees a replacement letter also sees the original
apex letter.
-/

noncomputable section

namespace GeneralSphereT.SimplicialCochain

open GeneralSphereT.PathAlgebra

variable {V G : Type*} [LinearOrder V] [Fintype V] [AddCommGroup G]
variable (K : AbstractSimplicialComplex V)

/-- Use the vertex order to give the closed-star coordinates the same fixed
colexicographic order as the Section 2 simplicial comparison. -/
local instance closedStarSimplexColexOrder
    (η : {s : Finset V // s ∈ K}) (n : ℕ) :
    LinearOrder (ClosedStarSimplex K η n) :=
  LinearOrder.lift'
    (fun τ : ClosedStarSimplex K η n => toColex τ.1.1)
    (by
      intro τ σ h
      apply Subtype.ext
      apply Subtype.ext
      exact (toColex : Finset V ≃ Colex (Finset V)).injective h)

/-- The ordered elementary word obtained from the active coordinates of
`bottom(t)`. -/
def coneBottomReplacementWord
    (η : {s : Finset V // s ∈ K}) (v : V) (hvη : v ∈ η.1) (n : ℕ)
    (t : ClosedStarCochain K η n G) :
    List (ClosedStarCochain K η n G) :=
  activeCoordinateIncrements (coneBottomReplacement K η v hvη n t)

/-- Every letter of the bottom word is a nonzero one-coordinate cochain. -/
theorem coneBottomReplacementWord_isElementary
    (η : {s : Finset V // s ∈ K}) (v : V) (hvη : v ∈ η.1) (n : ℕ)
    (t : ClosedStarCochain K η n G) :
    ∀ u ∈ coneBottomReplacementWord K η v hvη n t,
      IsElementaryLabel u := by
  intro u hu
  rcases List.mem_map.mp hu with ⟨σ, hσ, rfl⟩
  refine ⟨σ,
    coneBottomReplacement K η v hvη n t σ, ?_, rfl⟩
  exact Finsupp.mem_support_iff.mp (by
    simpa [coneBottomReplacementWord, activeCoordinateIncrements] using hσ)

private theorem wordIncrement_eq_sum {I : Type*} [AddCommGroup I]
    (word : List I) : wordIncrement word = word.sum := by
  induction word with
  | nil => rfl
  | cons u word ih => simp [wordIncrement, ih]

/-- Active coordinate increments add back to the original configuration. -/
theorem wordIncrement_activeCoordinateIncrements
    {ι A : Type*} [LinearOrder ι] [AddCommGroup A]
    (c : Configuration ι A) :
    wordIncrement (activeCoordinateIncrements c) = c := by
  rw [wordIncrement_eq_sum]
  ext i
  have h := congrArg (fun r : Configuration ι A => r i)
    (sum_single_support c)
  simpa [activeCoordinateIncrements] using h

/-- The total increment of the replacement word is literally `bottom(t)`. -/
theorem wordIncrement_coneBottomReplacementWord
    (η : {s : Finset V // s ∈ K}) (v : V) (hvη : v ∈ η.1) (n : ℕ)
    (t : ClosedStarCochain K η n G) :
    wordIncrement (coneBottomReplacementWord K η v hvη n t) =
      coneBottomReplacement K η v hvη n t := by
  exact wordIncrement_activeCoordinateIncrements
    (coneBottomReplacement K η v hvη n t)

/-- Consequently the replacement word and the original cochain have the same
configuration endpoint. -/
theorem closedStarCoboundary_wordIncrement_coneBottomReplacementWord
    (η : {s : Finset V // s ∈ K}) (v : V) (hvη : v ∈ η.1) (n : ℕ)
    (t : ClosedStarCochain K η n G) :
    closedStarCoboundary K η n
        (wordIncrement (coneBottomReplacementWord K η v hvη n t)) =
      closedStarCoboundary K η n t := by
  rw [wordIncrement_coneBottomReplacementWord,
    closedStarCoboundary_coneBottomReplacement]

/-! ## Carrier control for an elementary apex input -/

/-- Degree-`n` coordinates carried by a fixed vertex set. -/
def closedStarCarrierCoordinates
    (η : {s : Finset V // s ∈ K}) (n : ℕ) (ρ : Finset V) :
    Set (ClosedStarSimplex K η n) :=
  {σ | σ.1.1 ⊆ ρ}

/-- A letter in the replacement word remembers its unique active coordinate.
For an elementary apex input, that coordinate avoids the apex and contains
the original non-apex face. -/
theorem coneBottomReplacementWord_letter_coordinate
    (η : {s : Finset V // s ∈ K}) (v : V) (hvη : v ∈ η.1) (n : ℕ)
    (τ : ClosedStarSimplex K η n) (hvτ : v ∈ τ.1.1) (g : G)
    (u : ClosedStarCochain K η n G)
    (hu : u ∈ coneBottomReplacementWord K η v hvη n
      (Finsupp.single τ g)) :
    ∃ σ : ClosedStarSimplex K η n,
      σ ∈ (coneBottomReplacement K η v hvη n
        (Finsupp.single τ g)).support ∧
      u = Finsupp.single σ
        (coneBottomReplacement K η v hvη n
          (Finsupp.single τ g) σ) ∧
      v ∉ σ.1.1 ∧ τ.1.1.erase v ⊆ σ.1.1 := by
  rcases List.mem_map.mp hu with ⟨σ, hσ, rfl⟩
  have hσsupport : σ ∈
      (coneBottomReplacement K η v hvη n
        (Finsupp.single τ g)).support := by
    simpa [coneBottomReplacementWord, activeCoordinateIncrements] using hσ
  exact ⟨σ, hσsupport, rfl,
    coneBottomReplacement_single_support_coordinate
      K η v hvη n τ hvτ g σ hσsupport⟩

/-- Pure carrier form of support nonincrease.  If a cone carrier contains the
apex and contains the coordinate of a replacement letter, then it contains
the original apex coordinate. -/
theorem original_coordinate_mem_carrier_of_replacementWord_letter
    (η : {s : Finset V // s ∈ K}) (v : V) (hvη : v ∈ η.1) (n : ℕ)
    (τ : ClosedStarSimplex K η n) (hvτ : v ∈ τ.1.1) (g : G)
    (u : ClosedStarCochain K η n G)
    (hu : u ∈ coneBottomReplacementWord K η v hvη n
      (Finsupp.single τ g))
    (ρ : Finset V) (hvρ : v ∈ ρ)
    (huρ : coordinateRestriction (closedStarCarrierCoordinates K η n ρ) u ≠ 0) :
    τ ∈ closedStarCarrierCoordinates K η n ρ := by
  rcases coneBottomReplacementWord_letter_coordinate
    K η v hvη n τ hvτ g u hu with
      ⟨σ, _, rfl, _, hbase⟩
  have hσρ : σ ∈ closedStarCarrierCoordinates K η n ρ := by
    by_contra hnot
    exact huρ (coordinateRestriction_single_not_mem
      (closedStarCarrierCoordinates K η n ρ) hnot _)
  change τ.1.1 ⊆ ρ
  intro x hx
  by_cases hxv : x = v
  · simpa [hxv] using hvρ
  · have hxbase : x ∈ τ.1.1.erase v := Finset.mem_erase.mpr ⟨hxv, hx⟩
    exact hσρ (hbase hxbase)

/-- Coordinate-restriction form used directly as the visibility hypothesis of
the square-strip lemma. -/
theorem coneBottomReplacementWord_visibility
    (η : {s : Finset V // s ∈ K}) (v : V) (hvη : v ∈ η.1) (n : ℕ)
    (τ : ClosedStarSimplex K η n) (hvτ : v ∈ τ.1.1)
    (g : G) (hg : g ≠ 0)
    (u : ClosedStarCochain K η n G)
    (hu : u ∈ coneBottomReplacementWord K η v hvη n
      (Finsupp.single τ g))
    (ρ : Finset V) (hvρ : v ∈ ρ)
    (huρ : coordinateRestriction (closedStarCarrierCoordinates K η n ρ) u ≠ 0) :
    coordinateRestriction (closedStarCarrierCoordinates K η n ρ)
        (Finsupp.single τ g) ≠ 0 := by
  have hτρ : τ ∈ closedStarCarrierCoordinates K η n ρ :=
    original_coordinate_mem_carrier_of_replacementWord_letter
      K η v hvη n τ hvτ g u hu ρ hvρ huρ
  rw [coordinateRestriction_single_mem
    (closedStarCarrierCoordinates K η n ρ) hτρ]
  exact Finsupp.single_ne_zero.mpr hg

/-! ## Facet-data wrapper -/

section FacetVisibility

universe uF uB

variable {Facet : Type uF} {B : Type uB} [AddCommGroup B]
variable {BAt : Facet → Type*} [∀ ρ, AddCommGroup (BAt ρ)]

/-- The preceding coordinate statement packaged in exactly the form required
by `ellDistribution_elementaryCube_mem_physicalIdentityPaths`. -/
theorem coneBottomReplacementWord_facetVisibility
    {η : {s : Finset V // s ∈ K}} {n : ℕ}
    {d : ClosedStarCochain K η n G →+ B}
    (v : V) (hvη : v ∈ η.1)
    (facets : Facet → Finset V) (hvfacets : ∀ ρ, v ∈ facets ρ)
    (L : FacetRestrictionData
      (CAt := fun ρ => Configuration
        (closedStarCarrierCoordinates K η n (facets ρ)) G)
      (BAt := BAt) (Facet := Facet) d)
    (hprimitive : ∀ ρ,
      L.primitiveRes ρ = coordinateRestriction
        (closedStarCarrierCoordinates K η n (facets ρ)))
    (τ : ClosedStarSimplex K η n) (hvτ : v ∈ τ.1.1)
    (g : G) (hg : g ≠ 0)
    (u : ClosedStarCochain K η n G)
    (hu : u ∈ coneBottomReplacementWord K η v hvη n
      (Finsupp.single τ g)) (ρ : Facet)
    (huρ : L.primitiveRes ρ u ≠ 0) :
    L.primitiveRes ρ (Finsupp.single τ g) ≠ 0 := by
  rw [hprimitive ρ] at huρ ⊢
  exact coneBottomReplacementWord_visibility
    K η v hvη n τ hvτ g hg u hu (facets ρ) (hvfacets ρ) huρ

end FacetVisibility

end GeneralSphereT.SimplicialCochain
