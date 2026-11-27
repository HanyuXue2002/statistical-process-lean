import Formalization.ExplicitOrderedCellFilling
import Formalization.ElementaryPaths
import Formalization.Subdivision

set_option linter.style.header false

/-!
# Honest two-chain fillings for elementary primitive paths

The explicit one-edge filling extends by span induction to an existence
statement for every elementary path.  Thus the boundary-span formulation of
(2.31) is strengthened to the existence of an actual
`PrimitiveCellChain₂`.  No naturality is asserted for the noncanonical
choice-based filling function at the end of the file.
-/

noncomputable section

namespace GeneralSphereT.PathAlgebra

variable {ι G : Type*} [LinearOrder ι] [AddCommGroup G]

/--
Honest chain-level existence form of (2.31).  Every elementary primitive path
admits a primitive two-chain whose boundary is the difference between the
path and the canonical ordered path of its reduced boundary.
-/
theorem exists_primitiveCellChain₂_boundary_eq_sub_canonicalPath
    {p : Path (Configuration ι G) (Configuration ι G)}
    (hp : p ∈ elementaryPaths
      (ι := ι) (G := G) (X := Configuration ι G)) :
    ∃ Z : PrimitiveCellChain₂ ι G,
      primitiveCellBoundary₂ Z =
        p - canonicalPath
          (primitiveReducedBoundary (Configuration ι G) p) := by
  change p ∈ Submodule.span ℤ
    {q | ∃ (i : ι) (g : G) (c : Configuration ι G),
      g ≠ 0 ∧ q = edge (Finsupp.single i g) c} at hp
  induction hp using Submodule.span_induction with
  | mem p hp =>
      rcases hp with ⟨i, g, c, hg, rfl⟩
      refine ⟨explicitOrderedCellFilling c i g, ?_⟩
      rw [primitiveCellBoundary₂_explicitOrderedCellFilling_eq_loop]
      simp only [reducedBoundary_edge, AddMonoidHom.id_apply, map_sub,
        canonicalPath_redBracket]
      abel
  | zero =>
      exact ⟨0, by simp⟩
  | add p q hp hq ihp ihq =>
      rcases ihp with ⟨Z, hZ⟩
      rcases ihq with ⟨W, hW⟩
      refine ⟨Z + W, ?_⟩
      simp only [map_add, hZ, hW]
      abel
  | smul n p hp ih =>
      rcases ih with ⟨Z, hZ⟩
      refine ⟨n • Z, ?_⟩
      simp only [map_smul, hZ, smul_sub]

/-- A closed elementary primitive path is the boundary of an honest two-chain. -/
theorem exists_primitiveCellChain₂_boundary_eq_of_closedElementaryPath
    {p : Path (Configuration ι G) (Configuration ι G)}
    (helem : p ∈ elementaryPaths
      (ι := ι) (G := G) (X := Configuration ι G))
    (hclosed : primitiveReducedBoundary (Configuration ι G) p = 0) :
    ∃ Z : PrimitiveCellChain₂ ι G, primitiveCellBoundary₂ Z = p := by
  obtain ⟨Z, hZ⟩ :=
    exists_primitiveCellChain₂_boundary_eq_sub_canonicalPath helem
  refine ⟨Z, ?_⟩
  simpa [hclosed] using hZ

/--
A noncanonical filling selected for each elementary path.  This definition is
only a convenient witness extractor; no linearity or restriction naturality
is claimed.
-/
def chosenElementaryCellFilling
    (p : elementaryPaths
      (ι := ι) (G := G) (X := Configuration ι G)) :
    PrimitiveCellChain₂ ι G :=
  Classical.choose
    (exists_primitiveCellChain₂_boundary_eq_sub_canonicalPath p.property)

/-- Boundary specification of the noncanonical chosen filling. -/
theorem primitiveCellBoundary₂_chosenElementaryCellFilling
    (p : elementaryPaths
      (ι := ι) (G := G) (X := Configuration ι G)) :
    primitiveCellBoundary₂ (chosenElementaryCellFilling p) =
      (p : Path (Configuration ι G) (Configuration ι G)) -
        canonicalPath
          (primitiveReducedBoundary (Configuration ι G)
            (p : Path (Configuration ι G) (Configuration ι G))) :=
  Classical.choose_spec
    (exists_primitiveCellChain₂_boundary_eq_sub_canonicalPath p.property)

end GeneralSphereT.PathAlgebra
