import Formalization.Section4NormalizedChainDoldKanMap
import Formalization.RelativeDistributionLift

set_option linter.style.header false
set_option backward.isDefEq.respectTransparency false

/-!
# Section 4: global cochain distributions as genuine simplicial maps

Every global cochain gives the genuine `L`-valued map constructed through
normalized chains and Dold--Kan.  Evaluating those maps is additive in the
cochain, so an augmentation-zero integral distribution of global cochains
can be evaluated simplexwise.  The result is an actual simplicial map into
the reduced free abelian group on `L`, not merely a compatible family on
nondegenerate faces.
-/

noncomputable section

open CategoryTheory CategoryTheory.Category Opposite Simplicial

namespace GeneralSphereT.SimplicialCochain

open GeneralSphereT.PathAlgebra
open GeneralSphereT.StandardModels
open GeneralSphereT.Section4

universe u

variable {V G : Type u} [LinearOrder V] [Fintype V] [AddCommGroup G]

/-- Evaluation of the Dold--Kan map represented by a cochain at one
simplicial simplex.  Only the underlying set map is needed when a distribution
of cochains is pushed forward. -/
def cochainLValue
    (M : AbstractSimplicialComplex V) (q : ℕ)
    (Δ : SimplexCategoryᵒᵖ) (x : (orderedComplexSSet M).obj Δ) :
    Cochain M q G → (L (AddCommGrpCat.of G) (q + 1)).obj Δ :=
  fun c => (cochainToLMap M q c).app Δ x

/-- Evaluation commutes strictly with every face and degeneracy operator. -/
theorem cochainLValue_naturality
    (M : AbstractSimplicialComplex V) (q : ℕ)
    {Δ Δ' : SimplexCategoryᵒᵖ} (θ : Δ ⟶ Δ')
    (x : (orderedComplexSSet M).obj Δ) (c : Cochain M q G) :
    cochainLValue M q Δ' ((orderedComplexSSet M).map θ x) c =
      (L (AddCommGrpCat.of G) (q + 1)).map θ
        (cochainLValue M q Δ x c) := by
  change (cochainToLMap M q c).app Δ'
      ((orderedComplexSSet M).map θ x) =
    (L (AddCommGrpCat.of G) (q + 1)).map θ
      ((cochainToLMap M q c).app Δ x)
  exact cochainToLMap_naturality_apply M q c θ x

/-- Restrict an augmentation-zero distribution of global cochains to every
simplicial simplex.  Naturality is inherited from the genuine maps attached
to the individual cochains. -/
def globalCochainRestrictionMap
    (M : AbstractSimplicialComplex V) (q : ℕ)
    (u : RedDist (Cochain M q G)) :
    orderedComplexSSet M ⟶
      underlyingSSet (reducedFree (L (AddCommGrpCat.of G) (q + 1))) where
  app Δ := ↾fun x => mapRedDistFn (cochainLValue M q Δ x) u
  naturality Δ Δ' θ := by
    ext x
    change mapRedDistFn (cochainLValue M q Δ'
        ((orderedComplexSSet M).map θ x)) u =
      mapRedDist ((L (AddCommGrpCat.of G) (q + 1)).map θ).hom
        (mapRedDistFn (cochainLValue M q Δ x) u)
    rw [mapRedDist_eq_mapRedDistFn, mapRedDistFn_comp_apply]
    congr 2
    funext c
    exact cochainLValue_naturality M q θ x c

@[simp]
theorem globalCochainRestrictionMap_app_apply
    (M : AbstractSimplicialComplex V) (q : ℕ)
    (u : RedDist (Cochain M q G))
    (Δ : SimplexCategoryᵒᵖ) (x : (orderedComplexSSet M).obj Δ) :
    (globalCochainRestrictionMap M q u).app Δ x =
      mapRedDistFn (cochainLValue M q Δ x) u :=
  rfl

/-- The preceding construction is additive in the global distribution. -/
def globalCochainRestrictionHom
    (M : AbstractSimplicialComplex V) (q : ℕ) :
    RedDist (Cochain M q G) →+
      (orderedComplexSSet M ⟶
        underlyingSSet (reducedFree (L (AddCommGrpCat.of G) (q + 1)))) where
  toFun := globalCochainRestrictionMap M q
  map_zero' := by
    ext Δ x
    rfl
  map_add' u v := by
    ext Δ x
    change mapRedDistFn (cochainLValue M q Δ x) (u + v) =
      mapRedDistFn (cochainLValue M q Δ x) u +
        mapRedDistFn (cochainLValue M q Δ x) v
    exact map_add (mapRedDistFn (cochainLValue M q Δ x)) u v

/-- Integer-linear form of global simplexwise restriction. -/
def globalCochainRestrictionLinear
    (M : AbstractSimplicialComplex V) (q : ℕ) :
    RedDist (Cochain M q G) →ₗ[ℤ]
      (orderedComplexSSet M ⟶
        underlyingSSet (reducedFree (L (AddCommGrpCat.of G) (q + 1)))) :=
  (globalCochainRestrictionHom M q).toIntLinearMap

@[simp]
theorem globalCochainRestrictionLinear_apply
    (M : AbstractSimplicialComplex V) (q : ℕ)
    (u : RedDist (Cochain M q G)) :
    globalCochainRestrictionLinear M q u =
      globalCochainRestrictionMap M q u :=
  rfl

end GeneralSphereT.SimplicialCochain
