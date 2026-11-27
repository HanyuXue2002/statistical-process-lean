import Formalization.FiniteSimplicialCochain

set_option linter.style.header false

/-!
# Facet restriction data for finite simplicial cochains

This module instantiates the abstract facet API of the strict path model with
ordinary cochains on a finite ordered simplicial complex.  Facets are all
nonempty simplices of the complex.  Primitive restriction literally deletes
the coordinates not supported in a chosen simplex, while physical restriction
restricts a global coboundary to the corresponding local cochain group.
-/

noncomputable section

namespace GeneralSphereT.SimplicialCochain

open GeneralSphereT.PathAlgebra

/-- The facet index type used for a simplicial complex: all of its nonempty
simplices, in every dimension. -/
abbrev NonemptySimplex {V : Type*} (K : AbstractSimplicialComplex V) :=
  {s : Finset V // s ∈ K}

/-- Every degree-`n` simplex is visible in the facet given by that simplex
itself. -/
theorem simplex_mem_some_facesIn {V : Type*}
    (K : AbstractSimplicialComplex V) (n : ℕ) :
    ∀ η : Simplex K n,
      ∃ σ : NonemptySimplex K, η ∈ facesIn K n σ := by
  intro η
  exact ⟨⟨η.1, η.2.1⟩, Finset.Subset.rfl⟩

section RestrictionData

variable {V G : Type*} [LinearOrder V] [Fintype V] [AddCommGroup G]
variable (K : AbstractSimplicialComplex V) (n : ℕ)

/-- The abstract facet restriction package specialized to simplicial
cochains, with physical group the range of the global coboundary. -/
def facetRestrictionData :
    FacetRestrictionData
      (CAt := fun σ : NonemptySimplex K =>
        Configuration (facesIn K n σ) G)
      (BAt := fun σ : NonemptySimplex K =>
        Configuration (facesIn K (n + 1) σ) G)
      (Facet := NonemptySimplex K)
      (coboundaryToRange (G := G) K n) where
  primitiveRes σ := restrictCochain (G := G) K n σ
  physicalRes σ := restrictCoboundary (G := G) K n σ
  localD σ := (localCoboundary (G := G) K n σ).toAddMonoidHom
  commutes σ := by
    apply AddMonoidHom.ext
    intro c
    change restrictCochain (G := G) K (n + 1) σ
        (coboundary K n c) =
      localCoboundary K n σ (restrictCochain K n σ c)
    exact DFunLike.congr_fun
      (restrictCochain_coboundary (G := G) K n σ) c

/-- The global coboundary onto its range is surjective. -/
theorem facetCoboundary_surjective :
    Function.Surjective (coboundaryToRange (G := G) K n) :=
  coboundaryToRange_surjective K n

/-- Primitive facet restriction is literally coordinate deletion. -/
@[simp]
theorem facetRestrictionData_primitiveRes (σ : NonemptySimplex K) :
    (facetRestrictionData (G := G) K n).primitiveRes σ =
      coordinateRestriction (facesIn K n σ) :=
  rfl

omit [LinearOrder V] [Fintype V] in
/-- The chosen family of facets covers every cochain coordinate. -/
theorem facetRestrictionData_cover :
    ∀ η : Simplex K n,
      ∃ σ : NonemptySimplex K, η ∈ facesIn K n σ :=
  simplex_mem_some_facesIn K n

end RestrictionData

end GeneralSphereT.SimplicialCochain
