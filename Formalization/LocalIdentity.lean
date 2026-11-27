import Formalization.PrimitiveQuotient
import Formalization.Cells

set_option linter.style.header false

/-!
# Local identity squares

This file gives a Lean-friendly formulation of the ``no common facet''
condition.  A finite family is represented by `Fin n → I`: this retains
repeated increments, needs no decidable equality on `I`, and gives a witness
which can immediately be split in the two-increment case used by a square.

The square/local-vanishing core is independent of a choice of coordinates.
-/

noncomputable section

namespace GeneralSphereT.PathAlgebra

universe uF uI uC uB

section FiniteFacetCondition

variable {Facet : Type uF} {I : Type*} [AddCommGroup I]
variable {IAt : Facet → Type uI} [∀ ρ, AddCommGroup (IAt ρ)]

/--
No facet sees all increments in a finite indexed family: on every facet at
least one increment restricts to zero.

Using `Fin n → I`, rather than a `Finset I`, avoids both a decidable-equality
assumption and the accidental loss of repeated increments.
-/
def NoCommonFacet (res : ∀ ρ : Facet, I →+ IAt ρ)
    {n : ℕ} (increments : Fin n → I) : Prop :=
  ∀ ρ : Facet, ∃ k : Fin n, res ρ (increments k) = 0

/-- The finite family consisting of two increments. -/
def pairIncrements (s t : I) : Fin 2 → I :=
  fun k => Fin.cases s (fun _ => t) k

omit [AddCommGroup I] in
@[simp]
theorem pairIncrements_zero (s t : I) :
    pairIncrements s t 0 = s :=
  rfl

omit [AddCommGroup I] in
@[simp]
theorem pairIncrements_one (s t : I) :
    pairIncrements s t 1 = t :=
  rfl

/-- For two increments, `NoCommonFacet` is the expected facetwise disjunction. -/
theorem noCommonFacet_pair_iff
    (res : ∀ ρ : Facet, I →+ IAt ρ) (s t : I) :
    NoCommonFacet res (pairIncrements s t) ↔
      ∀ ρ : Facet, res ρ s = 0 ∨ res ρ t = 0 := by
  constructor
  · intro h ρ
    obtain ⟨k, hk⟩ := h ρ
    fin_cases k
    · exact Or.inl hk
    · exact Or.inr hk
  · intro h ρ
    rcases h ρ with hs | ht
    · exact ⟨0, by simpa using hs⟩
    · exact ⟨1, by simpa using ht⟩

end FiniteFacetCondition

section DifferenceOperators

variable {I X : Type*} [AddCommGroup I] [AddCommGroup X]

/-- The finite-difference operator `T_u - 1` on path base points. -/
def baseDifference (u : X) : Path I X →ₗ[ℤ] Path I X :=
  baseTranslation u - LinearMap.id

@[simp]
theorem baseDifference_edge (u : X) (r : I) (x : X) :
    baseDifference u (edge r x) = edge r (x + u) - edge r x := by
  simp [baseDifference]

/--
A cross-square is the difference of the two possible one-step base
differences.  This is the elementary locality generator used later.
-/
theorem square_eq_difference_commutator
    (φ : I →+ X) (s t : I) (x : X) :
    square φ s t x =
      baseDifference (φ s) (edge t x) -
        baseDifference (φ t) (edge s x) := by
  simp only [square, baseDifference_edge]
  abel

end DifferenceOperators

section PhysicalLocalitySquare

variable {C B : Type*} [AddCommGroup C] [AddCommGroup B]
variable {Facet : Type uF}
variable {CAt : Facet → Type uC} {BAt : Facet → Type uB}
variable [∀ ρ, AddCommGroup (CAt ρ)] [∀ ρ, AddCommGroup (BAt ρ)]
variable {d : C →+ B}

variable (L : FacetRestrictionData
  (CAt := CAt) (BAt := BAt) (Facet := Facet) d)

/-- A basic physical locality square. -/
def physicalLocalitySquare (d : C →+ B) (s t : C) (a : B) : Path C B :=
  square d s t a

/-- Restricting a physical square gives the square of the restricted data. -/
theorem restrictPhysicalPath_physicalLocalitySquare
    (ρ : Facet) (s t : C) (a : B) :
    L.restrictPhysicalPath ρ (physicalLocalitySquare d s t a) =
      square (L.localD ρ) (L.primitiveRes ρ s)
        (L.primitiveRes ρ t) (L.physicalRes ρ a) := by
  have hs : L.physicalRes ρ (d s) =
      L.localD ρ (L.primitiveRes ρ s) :=
    DFunLike.congr_fun (L.commutes ρ) s
  have ht : L.physicalRes ρ (d t) =
      L.localD ρ (L.primitiveRes ρ t) :=
    DFunLike.congr_fun (L.commutes ρ) t
  simp [physicalLocalitySquare, FacetRestrictionData.restrictPhysicalPath,
    square, hs, ht]

/-- Every basic physical locality square is a configuration cycle. -/
@[simp]
theorem configurationBoundary_physicalLocalitySquare
    (s t : C) (a : B) :
    configurationBoundary d (physicalLocalitySquare d s t a) = 0 := by
  exact boundary_square d s t a

/--
If no facet sees both increments, the physical square vanishes after every
facet restriction, hence belongs to the paper's local-zero path submodule.
-/
theorem physicalLocalitySquare_mem_locallyZeroPhysicalPath
    (s t : C) (a : B)
    (hst : NoCommonFacet L.primitiveRes (pairIncrements s t)) :
    physicalLocalitySquare d s t a ∈ L.locallyZeroPhysicalPath := by
  rw [FacetRestrictionData.locallyZeroPhysicalPath, Submodule.mem_iInf]
  intro ρ
  change L.restrictPhysicalPath ρ (physicalLocalitySquare d s t a) = 0
  rw [restrictPhysicalPath_physicalLocalitySquare]
  rcases (noCommonFacet_pair_iff L.primitiveRes s t).mp hst ρ with hs | ht
  · simp [hs]
  · simp [ht]

/-- The set of all basic squares satisfying the no-common-facet condition. -/
def physicalLocalitySquareGenerators : Set (Path C B) :=
  {R | ∃ s t : C, ∃ a : B,
    NoCommonFacet L.primitiveRes (pairIncrements s t) ∧
      R = physicalLocalitySquare d s t a}

/-- Integral combinations of basic physical locality squares. -/
def physicalLocalitySquareSpan : Submodule ℤ (Path C B) :=
  Submodule.span ℤ (physicalLocalitySquareGenerators L)

/-- Every basic generator lies in the configuration-cycle kernel. -/
theorem physicalLocalitySquareGenerators_subset_boundary_ker :
    physicalLocalitySquareGenerators L ⊆
      LinearMap.ker (configurationBoundary d) := by
  rintro R ⟨s, t, a, hst, rfl⟩
  change configurationBoundary d (physicalLocalitySquare d s t a) = 0
  exact configurationBoundary_physicalLocalitySquare (d := d) s t a

/-- Every basic generator is locally zero. -/
theorem physicalLocalitySquareGenerators_subset_locallyZero :
    physicalLocalitySquareGenerators L ⊆
      L.locallyZeroPhysicalPath := by
  rintro R ⟨s, t, a, hst, rfl⟩
  exact physicalLocalitySquare_mem_locallyZeroPhysicalPath L s t a hst

/-- The span of locality squares still consists entirely of cycles. -/
theorem physicalLocalitySquareSpan_le_boundary_ker :
    physicalLocalitySquareSpan L ≤
      LinearMap.ker (configurationBoundary d) := by
  rw [physicalLocalitySquareSpan, Submodule.span_le]
  exact physicalLocalitySquareGenerators_subset_boundary_ker L

/-- The span of locality squares still vanishes on every facet. -/
theorem physicalLocalitySquareSpan_le_locallyZeroPhysicalPath :
    physicalLocalitySquareSpan L ≤ L.locallyZeroPhysicalPath := by
  rw [physicalLocalitySquareSpan, Submodule.span_le]
  exact physicalLocalitySquareGenerators_subset_locallyZero L

/-- The basic square simultaneously has zero boundary and is locally zero. -/
theorem physicalLocalitySquare_is_local_cycle
    (s t : C) (a : B)
    (hst : NoCommonFacet L.primitiveRes (pairIncrements s t)) :
    configurationBoundary d (physicalLocalitySquare d s t a) = 0 ∧
      physicalLocalitySquare d s t a ∈ L.locallyZeroPhysicalPath :=
  ⟨configurationBoundary_physicalLocalitySquare (d := d) s t a,
    physicalLocalitySquare_mem_locallyZeroPhysicalPath L s t a hst⟩

end PhysicalLocalitySquare

end GeneralSphereT.PathAlgebra
