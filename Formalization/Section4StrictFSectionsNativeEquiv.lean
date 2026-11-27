import Formalization.Section4GlobalCochainRestrictionMap
import Formalization.Section4NativeFiberMaps
import Formalization.Section4DegreeZeroRow

set_option linter.style.header false

/-!
# Section 4: the formal passage from strict sections to native fibre maps

This file isolates the quotient argument in the identification

`StrictFSections M ≃ Hom_sSet(M, F(G,q+1))`.

The remaining geometric input is stated in its exact usable form.  Namely,
global simplexwise evaluation must (i) carry every algebraically compatible
representative to a map killed by `d_*`, (ii) have precisely the locally-zero
representatives as its kernel, and (iii) hit every map killed by `d_*`.
Once these three statements are available from the standard-simplex
classification and the cube-basis gluing argument, the equivalence below is
formal.
-/

noncomputable section

open CategoryTheory Opposite Simplicial

namespace GeneralSphereT.SimplicialCochain

open GeneralSphereT.PathAlgebra
open GeneralSphereT.PathAlgebra.FacetRestrictionData
open GeneralSphereT.Section4
open GeneralSphereT.StandardModels

universe u

variable {V G : Type u} [LinearOrder V] [Fintype V] [AddCommGroup G]
variable (M : AbstractSimplicialComplex V) (q : ℕ)

private abbrev LData := facetRestrictionData (G := G) M q

private abbrev NativeLMaps :=
  orderedComplexSSet M ⟶
    underlyingSSet (reducedFree (L (AddCommGrpCat.of G) (q + 1)))

private abbrev NativeKilledMaps :=
  MapsKilledByD (orderedComplexSSet M) (AddCommGrpCat.of G) (q + 1)

/-- Exact hypotheses still supplied by the local Dold--Kan evaluation and
cube-basis gluing calculation.  Keeping them together makes the boundary
between the formal quotient argument and the geometric input explicit. -/
structure StrictFSectionsNativeInput where
  killed :
    ∀ u : fCompatibleRedDist (LData (G := G) M q),
      postcomposeReducedFreeD (orderedComplexSSet M)
          (AddCommGrpCat.of G) (q + 1)
          (globalCochainRestrictionMap M q
            (u : RedDist (Cochain M q G))) = 0
  kernel :
    ∀ u : fCompatibleRedDist (LData (G := G) M q),
      globalCochainRestrictionMap M q
          (u : RedDist (Cochain M q G)) = 0 ↔
        u ∈ locallyZeroInFCompatible (LData (G := G) M q)
  surjective :
    ∀ f : NativeKilledMaps (G := G) M q,
      ∃ u : fCompatibleRedDist (LData (G := G) M q),
        globalCochainRestrictionMap M q
            (u : RedDist (Cochain M q G)) = f.1

variable (I : StrictFSectionsNativeInput (G := G) M q)

/-- Restrict a compatible global primitive distribution simplexwise and
remember that its genuine map is killed by `d_*`. -/
def fCompatibleToNativeKilled :
    fCompatibleRedDist (LData (G := G) M q) →ₗ[ℤ]
      NativeKilledMaps (G := G) M q where
  toFun u :=
    ⟨globalCochainRestrictionMap M q
        (u : RedDist (Cochain M q G)),
      AddMonoidHom.mem_ker.mpr (I.killed u)⟩
  map_add' u v := by
    apply Subtype.ext
    exact map_add (globalCochainRestrictionLinear M q)
      (u : RedDist (Cochain M q G))
      (v : RedDist (Cochain M q G))
  map_smul' n u := by
    apply Subtype.ext
    exact map_smul (globalCochainRestrictionLinear M q) n
      (u : RedDist (Cochain M q G))

@[simp]
theorem fCompatibleToNativeKilled_coe
    (u : fCompatibleRedDist (LData (G := G) M q)) :
    (fCompatibleToNativeKilled M q I u : NativeLMaps (G := G) M q) =
      globalCochainRestrictionMap M q
        (u : RedDist (Cochain M q G)) :=
  rfl

/-- The locally-zero denominator lies in the kernel of genuine
simplexwise evaluation. -/
theorem locallyZeroInFCompatible_le_ker_native :
    locallyZeroInFCompatible (LData (G := G) M q) ≤
      LinearMap.ker (fCompatibleToNativeKilled M q I) := by
  intro u hu
  rw [LinearMap.mem_ker]
  apply Subtype.ext
  exact (I.kernel u).2 hu

/-- The genuine restriction map descended to algebraic strict sections. -/
def strictFSectionsToNativeKilled :
    StrictFSections (LData (G := G) M q) →ₗ[ℤ]
      NativeKilledMaps (G := G) M q :=
  (locallyZeroInFCompatible (LData (G := G) M q)).liftQ
    (fCompatibleToNativeKilled M q I)
    (locallyZeroInFCompatible_le_ker_native M q I)

@[simp]
theorem strictFSectionsToNativeKilled_mkQ
    (u : fCompatibleRedDist (LData (G := G) M q)) :
    strictFSectionsToNativeKilled M q I
        ((locallyZeroInFCompatible (LData (G := G) M q)).mkQ u) =
      fCompatibleToNativeKilled M q I u :=
  rfl

/-- The kernel hypothesis is exactly what makes the descended map
injective. -/
theorem strictFSectionsToNativeKilled_injective :
    Function.Injective (strictFSectionsToNativeKilled M q I) := by
  rw [← LinearMap.ker_eq_bot]
  apply Submodule.ker_liftQ_eq_bot
  intro u hu
  exact (I.kernel u).1 (congrArg Subtype.val hu)

/-- The global-lift hypothesis is exactly what makes the descended map
surjective. -/
theorem strictFSectionsToNativeKilled_surjective :
    Function.Surjective (strictFSectionsToNativeKilled M q I) := by
  intro f
  obtain ⟨u, hu⟩ := I.surjective f
  refine ⟨(locallyZeroInFCompatible (LData (G := G) M q)).mkQ u, ?_⟩
  apply Subtype.ext
  exact hu

/-- Strict compatible sections are linearly equivalent to genuine maps into
`reducedFree L` killed by `d_*`. -/
def strictFSectionsLinearEquivNativeKilled :
    StrictFSections (LData (G := G) M q) ≃ₗ[ℤ]
      NativeKilledMaps (G := G) M q :=
  LinearEquiv.ofBijective (strictFSectionsToNativeKilled M q I)
    ⟨strictFSectionsToNativeKilled_injective M q I,
      strictFSectionsToNativeKilled_surjective M q I⟩

@[simp]
theorem strictFSectionsLinearEquivNativeKilled_apply_mkQ
    (u : fCompatibleRedDist (LData (G := G) M q)) :
    strictFSectionsLinearEquivNativeKilled M q I
        ((locallyZeroInFCompatible (LData (G := G) M q)).mkQ u) =
      fCompatibleToNativeKilled M q I u :=
  rfl

/-- Final native form: algebraic strict sections are the actual simplicial
maps from `M` to the categorical fibre `F(G,q+1)`. -/
def strictFSectionsAddEquivNativeFiberMaps :
    StrictFSections (LData (G := G) M q) ≃+
      (orderedComplexSSet M ⟶
        underlyingSSet (F (AddCommGrpCat.of G) (q + 1))) :=
  (strictFSectionsLinearEquivNativeKilled M q I).toAddEquiv.trans
    (MapsKilledByD.addEquivFiberMaps
      (orderedComplexSSet M) (AddCommGrpCat.of G) (q + 1))

end GeneralSphereT.SimplicialCochain
