import Formalization.ElementaryNaturality
import Formalization.LocalIdentity

set_option linter.style.header false

/-!
# The physical quotient: the basic-square core

This module gives the exact physical numerator and the part of the
physical denominator already covered by `LocalIdentity`: basic locality
squares with `k = 0`.  The full denominator also contains iterated base
differences and is deliberately not claimed here.

The two active increments of every generator are explicitly elementary.  This
bridges the coordinate-free square span of `LocalIdentity` with the paper's
elementary-expression subgroup.
-/

noncomputable section

namespace GeneralSphereT.PathAlgebra

universe uF uC uB

variable {ι G B : Type*}
variable [LinearOrder ι] [AddCommGroup G] [AddCommGroup B]
variable {Facet : Type uF}
variable {CAt : Facet → Type uC} {BAt : Facet → Type uB}
variable [∀ ρ, AddCommGroup (CAt ρ)] [∀ ρ, AddCommGroup (BAt ρ)]
variable {d : Configuration ι G →+ B}

variable (L : FacetRestrictionData
  (CAt := CAt) (BAt := BAt) (Facet := Facet) d)

/--
The exact physical numerator `E_inv`: elementary paths which are physical
cycles and vanish after restriction to every facet.
-/
def physicalInvariantPaths :
    Submodule ℤ (Path (Configuration ι G) B) :=
  elementaryPaths (ι := ι) (G := G) (X := B) ⊓
    (LinearMap.ker (configurationReducedBoundary d) ⊓
      L.locallyZeroPhysicalPath)

/--
Basic (`k = 0`) physical locality generators with both increments visibly
elementary and active.
-/
def elementaryPhysicalLocalitySquareGenerators :
    Set (Path (Configuration ι G) B) :=
  {R | ∃ (i : ι) (g : G) (j : ι) (h : G) (a : B),
    g ≠ 0 ∧ h ≠ 0 ∧
      NoCommonFacet L.primitiveRes
        (pairIncrements (Finsupp.single i g) (Finsupp.single j h)) ∧
      R = physicalLocalitySquare d
        (Finsupp.single i g) (Finsupp.single j h) a}

/--
The currently formalized part of the physical denominator: the integral span
of elementary basic locality squares (`k = 0` only).
-/
def physicalBasicSquareDenominator :
    Submodule ℤ (Path (Configuration ι G) B) :=
  Submodule.span ℤ (elementaryPhysicalLocalitySquareGenerators L)

omit [LinearOrder ι] in
/-- Every specialized generator is one of the coordinate-free generators. -/
theorem elementaryPhysicalLocalitySquareGenerators_subset_general :
    elementaryPhysicalLocalitySquareGenerators L ⊆
      physicalLocalitySquareGenerators L := by
  rintro R ⟨i, g, j, h, a, hg, hh, hst, rfl⟩
  exact ⟨Finsupp.single i g, Finsupp.single j h, a, hst, rfl⟩

omit [LinearOrder ι] in
/-- A square with two active elementary increments is an elementary path. -/
theorem elementaryPhysicalLocalitySquare_mem_elementaryPaths
    (i : ι) {g : G} (hg : g ≠ 0)
    (j : ι) {h : G} (hh : h ≠ 0) (a : B) :
    physicalLocalitySquare d
        (Finsupp.single i g) (Finsupp.single j h) a ∈
      elementaryPaths (ι := ι) (G := G) (X := B) := by
  let E := elementaryPaths (ι := ι) (G := G) (X := B)
  change
    edge (Finsupp.single i g) a +
          edge (Finsupp.single j h) (a + d (Finsupp.single i g)) -
        edge (Finsupp.single i g) (a + d (Finsupp.single j h)) -
      edge (Finsupp.single j h) a ∈ E
  exact E.sub_mem
    (E.sub_mem
      (E.add_mem
        (elementaryEdge_mem i hg a)
        (elementaryEdge_mem j hh (a + d (Finsupp.single i g))))
      (elementaryEdge_mem i hg (a + d (Finsupp.single j h))))
    (elementaryEdge_mem j hh a)

omit [LinearOrder ι] in
/-- Every elementary basic-square generator belongs to the elementary group. -/
theorem elementaryPhysicalLocalitySquareGenerators_subset_elementaryPaths :
    elementaryPhysicalLocalitySquareGenerators L ⊆
      elementaryPaths (ι := ι) (G := G) (X := B) := by
  rintro R ⟨i, g, j, h, a, hg, hh, hst, rfl⟩
  exact elementaryPhysicalLocalitySquare_mem_elementaryPaths
    (d := d) i hg j hh a

omit [LinearOrder ι] in
/-- The elementary basic-square span is contained in the general square span. -/
theorem physicalBasicSquareDenominator_le_generalSpan :
    physicalBasicSquareDenominator L ≤ physicalLocalitySquareSpan L := by
  rw [physicalBasicSquareDenominator, physicalLocalitySquareSpan,
    Submodule.span_le]
  intro R hR
  exact Submodule.subset_span
    (elementaryPhysicalLocalitySquareGenerators_subset_general L hR)

omit [LinearOrder ι] in
/-- The basic-square denominator is genuinely valued in elementary paths. -/
theorem physicalBasicSquareDenominator_le_elementaryPaths :
    physicalBasicSquareDenominator L ≤
      elementaryPaths (ι := ι) (G := G) (X := B) := by
  rw [physicalBasicSquareDenominator, Submodule.span_le]
  exact elementaryPhysicalLocalitySquareGenerators_subset_elementaryPaths L

omit [LinearOrder ι] in
/-- The basic-square denominator consists of reduced physical cycles. -/
theorem physicalBasicSquareDenominator_le_reducedBoundaryKer :
    physicalBasicSquareDenominator L ≤
      LinearMap.ker (configurationReducedBoundary d) := by
  rw [physicalBasicSquareDenominator, Submodule.span_le]
  rintro R ⟨i, g, j, h, a, hg, hh, hst, rfl⟩
  change configurationReducedBoundary d
      (physicalLocalitySquare d
        (Finsupp.single i g) (Finsupp.single j h) a) = 0
  apply Subtype.ext
  exact configurationBoundary_physicalLocalitySquare
    (d := d) (Finsupp.single i g) (Finsupp.single j h) a

omit [LinearOrder ι] in
/-- The basic-square denominator vanishes on every facet. -/
theorem physicalBasicSquareDenominator_le_locallyZeroPhysicalPath :
    physicalBasicSquareDenominator L ≤ L.locallyZeroPhysicalPath := by
  exact (physicalBasicSquareDenominator_le_generalSpan L).trans
    (physicalLocalitySquareSpan_le_locallyZeroPhysicalPath L)

omit [LinearOrder ι] in
/-- The basic-square (`k = 0`) denominator lies in the exact numerator. -/
theorem physicalBasicSquareDenominator_le_physicalInvariantPaths :
    physicalBasicSquareDenominator L ≤ physicalInvariantPaths L := by
  intro R hR
  exact ⟨physicalBasicSquareDenominator_le_elementaryPaths L hR,
    physicalBasicSquareDenominator_le_reducedBoundaryKer L hR,
    physicalBasicSquareDenominator_le_locallyZeroPhysicalPath L hR⟩

/-- The basic-square denominator regarded inside the physical numerator. -/
def physicalBasicSquareDenominatorInInvariantPaths :
    Submodule ℤ (physicalInvariantPaths L) :=
  Submodule.comap (physicalInvariantPaths L).subtype
    (physicalBasicSquareDenominator L)

/--
The typed quotient by the `k = 0` basic-square core.  This is not yet the full
physical quotient, whose denominator also contains iterated differences.
-/
abbrev PhysicalBasicSquareQuotient :=
  physicalInvariantPaths L ⧸
    physicalBasicSquareDenominatorInInvariantPaths L

end GeneralSphereT.PathAlgebra
