import Formalization.Section4BasedStrictNativeEquiv

set_option linter.style.header false

/-!
# Section 4: the degree-zero row in the actual pointed mapping group

The algebraic based row has already been proved exact.  Transporting it
through the strict-section/native-map equivalence gives the same exact row
with the middle term literally equal to the group of pointed simplicial maps
into the standard Dold--Kan fibre.
-/

noncomputable section

namespace GeneralSphereT.SimplicialCochain

open GeneralSphereT.PathAlgebra
open GeneralSphereT.PathAlgebra.FacetRestrictionData
open GeneralSphereT.Section4
open GeneralSphereT.StandardModels

universe u

variable {V G : Type u} [LinearOrder V] [Fintype V] [AddCommGroup G]

private abbrev LData (M : AbstractSimplicialComplex V) (q : ℕ) :=
  facetRestrictionData (G := G) M q

private abbrev TauData (M : AbstractSimplicialComplex V) (q : ℕ) :=
  Tau (fun σ : NonemptySimplex M ↦ facesIn M q σ) (LData (G := G) M q)

/-- The obstruction map (4.2), now defined on actual pointed maps. -/
def nativePointedObstruction
    (M : AbstractSimplicialComplex V) (b : V) (q : ℕ) :
    NativePointedMaps M b (AddCommGrpCat.of G) (q + 1) →ₗ[ℤ]
      TauData (G := G) M q :=
  (simplicialBasedObstruction (G := G) M b q).comp
    (basedStrictFSectionsLinearEquivNativePointedMaps
      (G := G) M b q).symm.toLinearMap

@[simp]
theorem nativePointedObstruction_on_based_section
    (M : AbstractSimplicialComplex V) (b : V) (q : ℕ)
    (x : (simplicialBasepointRowData (G := G) M b q).BasedSections) :
    nativePointedObstruction (G := G) M b q
        (basedStrictFSectionsLinearEquivNativePointedMaps (G := G) M b q x) =
      simplicialBasedObstruction (G := G) M b q x := by
  change simplicialBasedObstruction (G := G) M b q
      ((basedStrictFSectionsLinearEquivNativePointedMaps (G := G) M b q).symm
        (basedStrictFSectionsToNativePointedMap (G := G) M b q x)) = _
  rw [← basedStrictFSectionsLinearEquivNativePointedMaps_apply,
    LinearEquiv.symm_apply_apply]

/-- The actual pointed-map form of the middle exactness statement in (4.3). -/
theorem exact_basedRprimToNativePointedMap_nativePointedObstruction
    (M : AbstractSimplicialComplex V) (b : V) (q : ℕ) :
    Function.Exact (basedRprimToNativePointedMap M b q)
      (nativePointedObstruction (G := G) M b q) := by
  let E := basedStrictFSectionsLinearEquivNativePointedMaps (G := G) M b q
  have hexact := (simplicialBasedDegreeZeroRow (G := G) M b q).2.2.1
  intro f
  constructor
  · intro hf
    have hker : simplicialBasedObstruction (G := G) M b q (E.symm f) = 0 := by
      exact hf
    rcases (hexact (E.symm f)).mp hker with ⟨r, hr⟩
    refine ⟨r, ?_⟩
    calc
      basedRprimToNativePointedMap M b q r =
          basedStrictFSectionsToNativePointedMap (G := G) M b q
            ((simplicialBasepointRowData
              (G := G) M b q).basedRestriction r) := by
            have hcomp := LinearMap.congr_fun
              (basedStrictFSectionsToNativePointedMap_comp_basedRestriction
                (G := G) M b q) r
            exact hcomp.symm
      _ = E ((simplicialBasepointRowData
              (G := G) M b q).basedRestriction r) := rfl
      _ = E (E.symm f) := by rw [hr]
      _ = f := E.apply_symm_apply f
  · rintro ⟨r, rfl⟩
    change simplicialBasedObstruction (G := G) M b q
      (E.symm (basedRprimToNativePointedMap M b q r)) = 0
    have hmap : basedRprimToNativePointedMap M b q r =
        E ((simplicialBasepointRowData
          (G := G) M b q).basedRestriction r) := by
      have hcomp := LinearMap.congr_fun
        (basedStrictFSectionsToNativePointedMap_comp_basedRestriction
          (G := G) M b q) r
      exact hcomp.symm
    rw [hmap, E.symm_apply_apply]
    exact (hexact _).mpr ⟨r, rfl⟩

/-- The actual pointed obstruction is onto. -/
theorem nativePointedObstruction_surjective
    (M : AbstractSimplicialComplex V) (b : V) (q : ℕ) :
    Function.Surjective (nativePointedObstruction (G := G) M b q) := by
  let E := basedStrictFSectionsLinearEquivNativePointedMaps (G := G) M b q
  intro t
  rcases (simplicialBasedDegreeZeroRow (G := G) M b q).2.2.2 t with ⟨x, hx⟩
  refine ⟨E x, ?_⟩
  change simplicialBasedObstruction (G := G) M b q (E.symm (E x)) = t
  rw [E.symm_apply_apply]
  exact hx

/-- The full concrete degree-zero row with its mapping term interpreted
topologically rather than as an algebraic strict-section quotient. -/
theorem nativePointedDegreeZeroRow
    (M : AbstractSimplicialComplex V) (b : V) (q : ℕ) :
    Function.Injective
        (simplicialBasepointRowData (G := G) M b q).cyclesToBasedRelations ∧
      Function.Exact
        (simplicialBasepointRowData (G := G) M b q).cyclesToBasedRelations
        (basedRprimToNativePointedMap M b q) ∧
      Function.Exact (basedRprimToNativePointedMap M b q)
        (nativePointedObstruction (G := G) M b q) ∧
      Function.Surjective (nativePointedObstruction (G := G) M b q) := by
  have hrow := simplicialBasedDegreeZeroRow (G := G) M b q
  refine ⟨hrow.1, ?_,
    exact_basedRprimToNativePointedMap_nativePointedObstruction
      (G := G) M b q,
    nativePointedObstruction_surjective (G := G) M b q⟩
  intro r
  constructor
  · intro hr
    have hstrict :
        (simplicialBasepointRowData (G := G) M b q).basedRestriction r = 0 := by
      apply (basedStrictFSectionsToNativePointedMap_injective
        (G := G) M b q)
      have hcomp := LinearMap.congr_fun
        (basedStrictFSectionsToNativePointedMap_comp_basedRestriction
          (G := G) M b q) r
      calc
        basedStrictFSectionsToNativePointedMap (G := G) M b q
            ((simplicialBasepointRowData
              (G := G) M b q).basedRestriction r) =
          basedRprimToNativePointedMap M b q r := hcomp
        _ = 0 := hr
        _ = basedStrictFSectionsToNativePointedMap (G := G) M b q 0 :=
          (map_zero
            (basedStrictFSectionsToNativePointedMap (G := G) M b q)).symm
    exact (hrow.2.1 r).mp hstrict
  · rintro ⟨z, rfl⟩
    exact basedRprimToNativePointedMap_cycles_eq_zero M b q z

/-- Before identifying primitive images with nullhomotopic maps, exactness
already gives a choice-free quotient description of `tau` by actual pointed
maps. -/
def nativeThetaQuotientPrimitiveImage
    (M : AbstractSimplicialComplex V) (b : V) (q : ℕ) :
    TauData (G := G) M q ≃ₗ[ℤ]
      (NativePointedMaps M b (AddCommGrpCat.of G) (q + 1) ⧸
        LinearMap.range (basedRprimToNativePointedMap M b q)) :=
  targetEquivQuotientRange (basedRprimToNativePointedMap M b q)
    (nativePointedObstruction (G := G) M b q)
    (exact_basedRprimToNativePointedMap_nativePointedObstruction
      (G := G) M b q)
    (nativePointedObstruction_surjective (G := G) M b q)

@[simp]
theorem nativeThetaQuotientPrimitiveImage_obstruction
    (M : AbstractSimplicialComplex V) (b : V) (q : ℕ)
    (f : NativePointedMaps M b (AddCommGrpCat.of G) (q + 1)) :
    nativeThetaQuotientPrimitiveImage (G := G) M b q
        (nativePointedObstruction (G := G) M b q f) =
      (LinearMap.range (basedRprimToNativePointedMap M b q)).mkQ f :=
  targetEquivQuotientRange_apply (basedRprimToNativePointedMap M b q)
    (nativePointedObstruction (G := G) M b q)
    (exact_basedRprimToNativePointedMap_nativePointedObstruction
      (G := G) M b q)
    (nativePointedObstruction_surjective (G := G) M b q) f

end GeneralSphereT.SimplicialCochain
