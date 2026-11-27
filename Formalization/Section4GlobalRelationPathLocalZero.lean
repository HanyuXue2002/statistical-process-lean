import Formalization.CoordinateExtension
import Formalization.Section4GlobalCochainRestrictionNaturality
import Formalization.Section4StrictFSectionsNativeKilled

set_option linter.style.header false
set_option backward.isDefEq.respectTransparency false

/-!
# Section 4: locally zero relation paths vanish as genuine maps

The denominator condition in (4.19) says that a global relation path becomes
zero after restriction to every simplex.  Here that algebraic condition is
transported through the actual Dold--Kan evaluation: the resulting genuine
simplicial map into the relation-path object is identically zero, including
on degenerate simplices.
-/

noncomputable section

open CategoryTheory CategoryTheory.Category Opposite Simplicial

namespace GeneralSphereT.SimplicialCochain

open GeneralSphereT.PathAlgebra
open GeneralSphereT.PathAlgebra.FacetRestrictionData
open GeneralSphereT.StandardModels
open GeneralSphereT.Section4

universe u

variable {V G : Type u} [LinearOrder V] [Fintype V] [AddCommGroup G]

/-- Evaluation of the genuine `L`-valued map on a nondegenerate simplex
depends only on the cochain restricted to the support of that simplex. -/
theorem cochainLValue_eq_of_restrict_eq
    (M : AbstractSimplicialComplex V) (q n : ℕ)
    (x : (orderedComplexSSet M).nonDegenerate n)
    (c c' : Cochain M q G)
    (hcc' : restrictCochain M q (nonDegenerateSimplexFacet M x) c =
      restrictCochain M q (nonDegenerateSimplexFacet M x) c') :
    cochainLValue M q (Opposite.op (SimplexCategory.mk n)) x.1 c =
      cochainLValue M q (Opposite.op (SimplexCategory.mk n)) x.1 c' := by
  let F := nonDegenerateSimplexSupportMap M x
  have hpull : F.pullback (G := G) q c = F.pullback q c' := by
    rw [← localCochainToStandard_restrictCochain M x q c,
      ← localCochainToStandard_restrictCochain M x q c']
    exact congrArg (localCochainToStandard M x q) hcc'
  have hc := ConcreteCategory.congr_hom
    (NatTrans.congr_app (cochainToLMap_pullback F q c)
      (Opposite.op (SimplexCategory.mk n)))
        (nonDegenerateSimplexSupportTop M x)
  have hc' := ConcreteCategory.congr_hom
    (NatTrans.congr_app (cochainToLMap_pullback F q c')
      (Opposite.op (SimplexCategory.mk n)))
        (nonDegenerateSimplexSupportTop M x)
  change cochainLValue M q _ x.1 c =
      (cochainToLMap (nonDegenerateSimplexSupportComplex M x) q
        (F.pullback q c)).app _
          (nonDegenerateSimplexSupportTop M x) at hc
  change cochainLValue M q _ x.1 c' =
      (cochainToLMap (nonDegenerateSimplexSupportComplex M x) q
        (F.pullback q c')).app _
          (nonDegenerateSimplexSupportTop M x) at hc'
  calc
    _ = (cochainToLMap (nonDegenerateSimplexSupportComplex M x) q
        (F.pullback q c)).app _
          (nonDegenerateSimplexSupportTop M x) := hc
    _ = (cochainToLMap (nonDegenerateSimplexSupportComplex M x) q
        (F.pullback q c')).app _
          (nonDegenerateSimplexSupportTop M x) := by rw [hpull]
    _ = _ := hc'.symm

/-- An additive local evaluation map, obtained by extension by zero. -/
def localCochainLValueHom
    (M : AbstractSimplicialComplex V) (q n : ℕ)
    (x : (orderedComplexSSet M).nonDegenerate n) :
    Configuration (facesIn M q (nonDegenerateSimplexFacet M x)) G →+
      (L (AddCommGrpCat.of G) (q + 1)).obj
        (Opposite.op (SimplexCategory.mk n)) :=
  (cochainLValueHom M q _ x.1).comp
    (coordinateExtension
      (facesIn M q (nonDegenerateSimplexFacet M x)))

/-- The local evaluation factors the global one through restriction to the
support simplex. -/
theorem localCochainLValueHom_restrict
    (M : AbstractSimplicialComplex V) (q n : ℕ)
    (x : (orderedComplexSSet M).nonDegenerate n)
    (c : Cochain M q G) :
    localCochainLValueHom M q n x
        (restrictCochain M q (nonDegenerateSimplexFacet M x) c) =
      cochainLValueHom M q _ x.1 c := by
  apply cochainLValue_eq_of_restrict_eq M q n x
  exact coordinateRestriction_coordinateExtension
    (facesIn M q (nonDegenerateSimplexFacet M x))
      (restrictCochain M q (nonDegenerateSimplexFacet M x) c)

/-- On a nondegenerate simplex, local vanishing of a normalized global path
forces its evaluated relation path to vanish. -/
theorem globalRelationPathValue_eq_zero_of_locallyZero
    (M : AbstractSimplicialComplex V) (q n : ℕ)
    (R : LinearMap.ker
      (mapDNormalizedPath (coboundaryToRange (G := G) M q)))
    (hlocal : R.1.1 ∈
      locallyZeroPrimitivePath (facetRestrictionData (G := G) M q))
    (x : (orderedComplexSSet M).nonDegenerate n) :
    globalRelationPathValue M q R
      (Opposite.op (SimplexCategory.mk n)) x.1 = 0 := by
  let σ := nonDegenerateSimplexFacet M x
  have hσ : mapPath
      (restrictCochain (G := G) M q σ)
      (restrictCochain (G := G) M q σ) R.1.1 = 0 := by
    exact LinearMap.mem_ker.mp
      ((Submodule.mem_iInf (fun τ : NonemptySimplex M ↦
        LinearMap.ker
          ((facetRestrictionData (G := G) M q).restrictPrimitivePath τ))).mp
            hlocal σ)
  have hfactor :
      cochainLValueHom M q _ x.1 =
        (localCochainLValueHom M q n x).comp
          (restrictCochain (G := G) M q σ) := by
    apply AddMonoidHom.ext
    intro c
    exact (localCochainLValueHom_restrict M q n x c).symm
  apply Subtype.ext
  apply Subtype.ext
  change mapPath (cochainLValueHom M q _ x.1)
      (cochainLValueHom M q _ x.1) R.1.1 = 0
  calc
    _ = mapPath
        ((localCochainLValueHom M q n x).comp
          (restrictCochain (G := G) M q σ))
        ((localCochainLValueHom M q n x).comp
          (restrictCochain (G := G) M q σ)) R.1.1 := by rw [hfactor]
    _ = mapPath (localCochainLValueHom M q n x)
        (localCochainLValueHom M q n x)
        (mapPath (restrictCochain (G := G) M q σ)
          (restrictCochain (G := G) M q σ) R.1.1) :=
      (mapPath_comp_apply
        (restrictCochain (G := G) M q σ)
        (restrictCochain (G := G) M q σ)
        (localCochainLValueHom M q n x)
        (localCochainLValueHom M q n x) R.1.1).symm
    _ = 0 := by rw [hσ, map_zero]

/-- A locally zero global relation path gives the zero genuine simplicial
map, with the degenerate cases supplied by simplicial naturality. -/
theorem globalRelationPathRestrictionMap_eq_zero_of_locallyZero
    (M : AbstractSimplicialComplex V) (q : ℕ)
    (R : LinearMap.ker
      (mapDNormalizedPath (coboundaryToRange (G := G) M q)))
    (hlocal : R.1.1 ∈
      locallyZeroPrimitivePath (facetRestrictionData (G := G) M q)) :
    globalRelationPathRestrictionMap M q R = 0 := by
  ext Δ z
  induction Δ using Opposite.rec with
  | _ Δ =>
    induction Δ using SimplexCategory.rec with
    | _ n =>
      obtain ⟨m, f, _, y, hz⟩ :=
        (orderedComplexSSet M).exists_nonDegenerate z
      rw [hz]
      have hy := globalRelationPathValue_eq_zero_of_locallyZero
        M q m R hlocal y
      calc
        _ = (simplicialRelationPath
              (d (AddCommGrpCat.of G) (q + 1))).map f.op
              ((globalRelationPathRestrictionMap M q R).app
                (Opposite.op (SimplexCategory.mk m)) y.1) := by
            exact underlyingSSetMap_naturality_apply
              (globalRelationPathRestrictionMap M q R) f.op y.1
        _ = 0 := by rw [globalRelationPathRestrictionMap_app_apply, hy,
          map_zero]

/-- Bundle a denominator relation path as the normalized kernel element used
by the genuine relation-path object. -/
def relationPathKernel
    (M : AbstractSimplicialComplex V) (q : ℕ)
    (R : relationPaths (facetRestrictionData (G := G) M q)) :
    LinearMap.ker
      (mapDNormalizedPath (coboundaryToRange (G := G) M q)) := by
  refine ⟨⟨R.1, R.2.1⟩, ?_⟩
  apply Subtype.ext
  exact R.2.2.1

@[simp]
theorem relationPathKernel_coe
    (M : AbstractSimplicialComplex V) (q : ℕ)
    (R : relationPaths (facetRestrictionData (G := G) M q)) :
    (relationPathKernel M q R).1.1 = R.1 :=
  rfl

/-- The genuine map attached to a denominator relation path is zero. -/
theorem relationPath_globalRestriction_eq_zero
    (M : AbstractSimplicialComplex V) (q : ℕ)
    (R : relationPaths (facetRestrictionData (G := G) M q)) :
    globalRelationPathRestrictionMap M q (relationPathKernel M q R) = 0 :=
  globalRelationPathRestrictionMap_eq_zero_of_locallyZero M q
    (relationPathKernel M q R) R.2.2.2

end GeneralSphereT.SimplicialCochain
