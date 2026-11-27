import Formalization.IteratedLocality

set_option linter.style.header false

/-!
# Primitive lifts of physical locality identities

This module formalizes the easy inclusion in Lemma (2.26).
Surjectivity of `d` is used exactly once: to lift the physical base point of a
locality square.  The active increments and every transverse difference already
live in the primitive configuration group, so they require no choices.
-/

noncomputable section

namespace GeneralSphereT.PathAlgebra

universe uF uC uB

section PrimitiveWord

variable {C B : Type*} [AddCommGroup C] [AddCommGroup B]
variable {Facet : Type uF}
variable {CAt : Facet → Type uC} {BAt : Facet → Type uB}
variable [∀ ρ, AddCommGroup (CAt ρ)] [∀ ρ, AddCommGroup (BAt ρ)]
variable {d : C →+ B}

variable (L : FacetRestrictionData
  (CAt := CAt) (BAt := BAt) (Facet := Facet) d)

/-- The primitive version of a full iterated locality square. -/
def iteratedPrimitiveLocalitySquare
    (s t : C) (rs : List C) (c : C) : Path C C :=
  iteratedPhysicalLocalitySquare (AddMonoidHom.id C) s t rs c

/-- Applying `d_*` to a primitive iterated square changes only its base point. -/
theorem mapDPath_iteratedPrimitiveLocalitySquare
    (s t : C) (rs : List C) (c : C) :
    mapDPath d (iteratedPrimitiveLocalitySquare s t rs c) =
      iteratedPhysicalLocalitySquare d s t rs (d c) := by
  change
    mapPath (AddMonoidHom.id C) d
        (iteratedBaseDifference (AddMonoidHom.id C) rs
          (physicalLocalitySquare (AddMonoidHom.id C) s t c)) =
      iteratedBaseDifference d rs (physicalLocalitySquare d s t (d c))
  rw [mapPath_iteratedBaseDifference_apply
    (AddMonoidHom.id C) d (AddMonoidHom.id C) d rfl]
  simp [physicalLocalitySquare, square]

/-- A primitive iterated square is a closed primitive word. -/
theorem primitiveBoundary_iteratedPrimitiveLocalitySquare
    (s t : C) (rs : List C) (c : C) :
    primitiveBoundary C (iteratedPrimitiveLocalitySquare s t rs c) = 0 := by
  exact configurationBoundary_iteratedPhysicalLocalitySquare
    (d := AddMonoidHom.id C) s t rs c

/-- Restricting a primitive iterated square is the corresponding local word. -/
theorem restrictPrimitivePath_iteratedPrimitiveLocalitySquare
    (ρ : Facet) (s t : C) (rs : List C) (c : C) :
    L.restrictPrimitivePath ρ
        (iteratedPrimitiveLocalitySquare s t rs c) =
      iteratedBaseDifference (AddMonoidHom.id (CAt ρ))
        (rs.map (L.primitiveRes ρ))
        (physicalLocalitySquare (AddMonoidHom.id (CAt ρ))
          (L.primitiveRes ρ s) (L.primitiveRes ρ t)
          (L.primitiveRes ρ c)) := by
  change
    mapPath (L.primitiveRes ρ) (L.primitiveRes ρ)
        (iteratedBaseDifference (AddMonoidHom.id C) rs
          (physicalLocalitySquare (AddMonoidHom.id C) s t c)) = _
  rw [mapPath_iteratedBaseDifference_apply
    (AddMonoidHom.id C) (AddMonoidHom.id (CAt ρ))
    (L.primitiveRes ρ) (L.primitiveRes ρ) rfl]
  simp [physicalLocalitySquare, square]

/-- The no-common-facet condition makes the primitive lift locally zero. -/
theorem iteratedPrimitiveLocalitySquare_mem_locallyZeroPrimitivePath
    (s t : C) (rs : List C) (c : C)
    (hst : NoCommonFacetList L.primitiveRes (s :: t :: rs)) :
    iteratedPrimitiveLocalitySquare s t rs c ∈
      L.locallyZeroPrimitivePath := by
  rw [FacetRestrictionData.locallyZeroPrimitivePath, Submodule.mem_iInf]
  intro ρ
  change L.restrictPrimitivePath ρ
    (iteratedPrimitiveLocalitySquare s t rs c) = 0
  rw [restrictPrimitivePath_iteratedPrimitiveLocalitySquare L]
  obtain ⟨r, hr, hρ⟩ :=
    (noCommonFacetList_iff L.primitiveRes (s :: t :: rs)).mp hst ρ
  simp only [List.mem_cons] at hr
  rcases hr with rfl | rfl | hr
  · simp [physicalLocalitySquare, hρ]
  · simp [physicalLocalitySquare, hρ]
  · apply iteratedBaseDifference_eq_zero_of_mem_ker
      (r := L.primitiveRes ρ r)
    · exact List.mem_map.mpr ⟨r, hr, rfl⟩
    · simp [hρ]

end PrimitiveWord

section ElementaryPrimitiveLift

variable {ι G B : Type*}
variable [LinearOrder ι] [AddCommGroup G] [AddCommGroup B]
variable {Facet : Type uF}
variable {CAt : Facet → Type uC} {BAt : Facet → Type uB}
variable [∀ ρ, AddCommGroup (CAt ρ)] [∀ ρ, AddCommGroup (BAt ρ)]
variable {d : Configuration ι G →+ B}

variable (L : FacetRestrictionData
  (CAt := CAt) (BAt := BAt) (Facet := Facet) d)

/-- Elementary, closed, and locally zero primitive words: the source in the
easy inclusion of (2.26). -/
def closedLocallyZeroElementaryPrimitivePaths :
    Submodule ℤ
      (Path (Configuration ι G) (Configuration ι G)) :=
  elementaryPaths (ι := ι) (G := G) (X := Configuration ι G) ⊓
    (LinearMap.ker (primitiveReducedBoundary (Configuration ι G)) ⊓
      L.locallyZeroPrimitivePath)

omit [LinearOrder ι] in
/-- The complete package for one primitive lift. -/
theorem primitiveLocalityGenerator_lift
    (hd : Function.Surjective d)
    (i : ι) (g : G) (j : ι) (h : G)
    (rs : List (Configuration ι G)) (a : B)
    (hg : g ≠ 0) (hh : h ≠ 0)
    (hst : NoCommonFacetList L.primitiveRes
      (Finsupp.single i g :: Finsupp.single j h :: rs)) :
    ∃ W : Path (Configuration ι G) (Configuration ι G),
      mapDPath d W = iteratedPhysicalLocalitySquare d
        (Finsupp.single i g) (Finsupp.single j h) rs a ∧
      W ∈ elementaryPaths (ι := ι) (G := G)
        (X := Configuration ι G) ∧
      primitiveBoundary (Configuration ι G) W = 0 ∧
      W ∈ L.locallyZeroPrimitivePath := by
  obtain ⟨c, rfl⟩ := hd a
  let W := iteratedPrimitiveLocalitySquare
    (Finsupp.single i g) (Finsupp.single j h) rs c
  refine ⟨W, ?_, ?_, ?_, ?_⟩
  · exact mapDPath_iteratedPrimitiveLocalitySquare
      (d := d) (Finsupp.single i g) (Finsupp.single j h) rs c
  · exact iteratedPhysicalLocalitySquare_mem_elementaryPaths
      (AddMonoidHom.id (Configuration ι G)) i hg j hh rs c
  · exact primitiveBoundary_iteratedPrimitiveLocalitySquare
      (Finsupp.single i g) (Finsupp.single j h) rs c
  · exact iteratedPrimitiveLocalitySquare_mem_locallyZeroPrimitivePath
      L (Finsupp.single i g) (Finsupp.single j h) rs c hst

omit [LinearOrder ι] in
/-- Every physical locality generator has a primitive lift satisfying all three
conditions in the left-hand side of (2.26). -/
theorem physicalLocalityIdentityGenerator_has_primitive_lift
    (hd : Function.Surjective d) {R : Path (Configuration ι G) B}
    (hR : R ∈ physicalLocalityIdentityGenerators L) :
    ∃ W : Path (Configuration ι G) (Configuration ι G),
      mapDPath d W = R ∧
      W ∈ closedLocallyZeroElementaryPrimitivePaths L := by
  rcases hR with ⟨i, g, j, h, rs, a, hg, hh, hst, rfl⟩
  obtain ⟨W, hdW, hel, hbd, hloc⟩ :=
    primitiveLocalityGenerator_lift L hd i g j h rs a hg hh hst
  refine ⟨W, hdW, hel, ?_, hloc⟩
  change primitiveReducedBoundary (Configuration ι G) W = 0
  apply Subtype.ext
  exact hbd

omit [LinearOrder ι] in
/-- Span-level easy inclusion in Lemma (2.26): the full physical denominator
is contained in the `d_*`-image of closed, locally zero elementary primitive
words. -/
theorem physicalIdentityPaths_le_mapDPath_closedPrimitive
    (hd : Function.Surjective d) :
    physicalIdentityPaths L ≤
      Submodule.map (mapDPath d)
        (closedLocallyZeroElementaryPrimitivePaths L) := by
  rw [physicalIdentityPaths, Submodule.span_le]
  intro R hR
  obtain ⟨W, hdW, hW⟩ :=
    physicalLocalityIdentityGenerator_has_primitive_lift L hd hR
  exact ⟨W, hW, hdW⟩

end ElementaryPrimitiveLift

end GeneralSphereT.PathAlgebra
