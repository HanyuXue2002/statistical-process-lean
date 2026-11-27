import Formalization.Section4NativeMapCubeCompatibility
import Formalization.Section4GlobalRestrictionCompatibleOfKilled

set_option linter.style.header false
set_option backward.isDefEq.respectTransparency false

/-!
# Surjectivity of global cochain-distribution evaluation

The local `L`-classification pulls a native simplicial map back to a reduced
distribution of cochains on every simplex.  Simplicial naturality makes the
Boolean-cube coefficients compatible, so the integral cube-gluing theorem
produces one global reduced distribution with exactly those restrictions.
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

local instance nativeSurjectiveSimplexColexOrder : LinearOrder (Simplex M q) :=
  LinearOrder.lift'
    (fun η : Simplex M q => toColex η.1)
    ((toColex : Finset V ≃ Colex (Finset V)).injective.comp
      Subtype.val_injective)

local instance nativeSurjectiveFacetFintype : Fintype (NonemptySimplex M) :=
  Fintype.ofFinite _

/-- Glue the local cochain distributions classified by a native map. -/
def nativeMapGlobalDistribution
    (f : orderedComplexSSet M ⟶
      underlyingSSet (reducedFree (L (AddCommGrpCat.of G) (q + 1)))) :
    RedDist (Cochain M q G) :=
  glueReducedDistributions
    (fun σ : NonemptySimplex M => facesIn M q σ)
    (nativeMapLocalDistribution M q f)

/-- The glued distribution has exactly the prescribed restriction on every
simplex. -/
theorem nativeMapGlobalDistribution_restriction
    (f : orderedComplexSSet M ⟶
      underlyingSSet (reducedFree (L (AddCommGrpCat.of G) (q + 1))))
    (σ : NonemptySimplex M) :
    mapRedDist (restrictCochain (G := G) M q σ)
        (nativeMapGlobalDistribution M q f) =
      nativeMapLocalDistribution M q f σ := by
  exact mapRedDist_glueReducedDistributions
    (fun τ : NonemptySimplex M => facesIn M q τ)
    (nativeMapLocalDistribution M q f)
    (nativeMapLocalDistribution_cubeCoefficientCompatible
      (G := G) M q f) σ

/-- Global cochain evaluation factors through the local top-simplex
classification on a chosen facet. -/
theorem cochainLValueHom_factor_facet
    (σ : NonemptySimplex M) :
    cochainLValueHom (G := G) M q
        (Opposite.op
          (SimplexCategory.mk (nonemptySimplexDimension σ)))
        (nonemptySimplexNonDegenerate M σ).1 =
      (facetCochainLValueHom (G := G) M q σ).comp
        (restrictCochain (G := G) M q σ) := by
  apply AddMonoidHom.ext
  intro c
  change cochainLValueHom (G := G) M q _
      (nonemptySimplexNonDegenerate M σ).1 c =
    facetCochainLValueHom M q σ
      (restrictCochain M q σ c)
  rw [facetCochainLValueHom_apply]
  let x := nonemptySimplexNonDegenerate M σ
  apply cochainLValue_eq_of_restrict_eq M q _ x
  change coordinateRestriction
      (facesIn M q (nonDegenerateSimplexFacet M x)) c =
    coordinateRestriction
      (facesIn M q (nonDegenerateSimplexFacet M x))
        (coordinateExtension (facesIn M q σ)
          (coordinateRestriction (facesIn M q σ) c))
  rw [show nonDegenerateSimplexFacet M x = σ by
    exact nonemptySimplexNonDegenerate_facet M σ]
  rw [coordinateRestriction_coordinateExtension]

/-- On every canonical nondegenerate simplex, evaluation of the glued
distribution recovers the original native map. -/
theorem nativeMapGlobalRestriction_canonical
    (f : orderedComplexSSet M ⟶
      underlyingSSet (reducedFree (L (AddCommGrpCat.of G) (q + 1))))
    (σ : NonemptySimplex M) :
    (globalCochainRestrictionMap M q
      (nativeMapGlobalDistribution M q f)).app
        (Opposite.op
          (SimplexCategory.mk (nonemptySimplexDimension σ)))
          (nonemptySimplexNonDegenerate M σ).1 =
      f.app (Opposite.op
        (SimplexCategory.mk (nonemptySimplexDimension σ)))
          (nonemptySimplexNonDegenerate M σ).1 := by
  rw [globalCochainRestrictionMap_app_apply]
  change mapRedDist
      (cochainLValueHom (G := G) M q _
        (nonemptySimplexNonDegenerate M σ).1)
      (nativeMapGlobalDistribution M q f) = _
  rw [cochainLValueHom_factor_facet]
  rw [← GeneralSphereT.StandardModels.mapRedDist_comp_apply]
  rw [nativeMapGlobalDistribution_restriction]
  exact mapRedDist_facetCochainLValue_nativeMapLocalDistribution
    (G := G) M q f σ

/-- The facet of a nondegenerate `n`-simplex has dimension `n`. -/
theorem nonemptySimplexDimension_nonDegenerateSimplexFacet
    {n : ℕ} (x : (orderedComplexSSet M).nonDegenerate n) :
    nonemptySimplexDimension (nonDegenerateSimplexFacet M x) = n := by
  unfold nonemptySimplexDimension
  have hcard := (nonDegenerateSimplexEquiv M n x).2.2
  change (orderedSimplexSupport x.1.1).card = n + 1 at hcard
  change (orderedSimplexSupport x.1.1).card - 1 = n
  omega

/-- After identifying dimensions, the canonical representative of the
facet of a nondegenerate simplex is that simplex itself. -/
theorem nonemptySimplexNonDegenerate_facet_self
    {n : ℕ} (x : (orderedComplexSSet M).nonDegenerate n)
    (h : nonemptySimplexDimension
      (nonDegenerateSimplexFacet M x) = n) :
    h ▸ nonemptySimplexNonDegenerate M
        (nonDegenerateSimplexFacet M x) = x := by
  let d := nonemptySimplexDimension (nonDegenerateSimplexFacet M x)
  let z : (orderedComplexSSet M).nonDegenerate d :=
    nonemptySimplexNonDegenerate M (nonDegenerateSimplexFacet M x)
  let supportFn : ∀ k : ℕ,
      (orderedComplexSSet M).nonDegenerate k → Finset V :=
    fun _ y => orderedSimplexSupport y.1.1
  have hd : d = n := h
  have hfun : supportFn n ≍ supportFn d :=
    (congr_arg_heq supportFn hd).symm
  have hz0 :=
    @eqRec_heq ℕ
      (fun k => (orderedComplexSSet M).nonDegenerate k)
      d n hd z
  have hz : (hd ▸ z) ≍ z := hz0
  have hsupp : supportFn n (hd ▸ z) = supportFn d z :=
    congr_heq hfun hz
  have hzsupport : supportFn d z = supportFn n x := by
    exact congrArg Subtype.val
      (nonemptySimplexNonDegenerate_facet M
        (nonDegenerateSimplexFacet M x))
  apply (nonDegenerateSimplexEquiv M _).injective
  apply Subtype.ext
  change supportFn n (hd ▸ z) = supportFn n x
  exact hsupp.trans hzsupport

/-- The glued global distribution evaluates to the original native map. -/
theorem nativeMapGlobalRestriction_eq
    (f : orderedComplexSSet M ⟶
      underlyingSSet (reducedFree (L (AddCommGrpCat.of G) (q + 1)))) :
    globalCochainRestrictionMap M q
        (nativeMapGlobalDistribution M q f) = f := by
  ext Δ z
  induction Δ using Opposite.rec with
  | _ Δ =>
    induction Δ using SimplexCategory.rec with
    | _ n =>
      obtain ⟨m, θ, _, y, hz⟩ :=
        (orderedComplexSSet M).exists_nonDegenerate z
      rw [hz]
      let σ := nonDegenerateSimplexFacet M y
      have hdim : nonemptySimplexDimension σ = m :=
        nonemptySimplexDimension_nonDegenerateSimplexFacet M y
      have hy : hdim ▸ nonemptySimplexNonDegenerate M σ = y :=
        nonemptySimplexNonDegenerate_facet_self M y hdim
      have hcanonical := nativeMapGlobalRestriction_canonical
        (G := G) M q f σ
      have htop :
          (globalCochainRestrictionMap M q
            (nativeMapGlobalDistribution M q f)).app
              (Opposite.op (SimplexCategory.mk m)) y.1 =
            f.app (Opposite.op (SimplexCategory.mk m)) y.1 := by
        let P : ∀ k : ℕ,
            (orderedComplexSSet M).nonDegenerate k → Prop :=
          fun k t =>
            (globalCochainRestrictionMap M q
              (nativeMapGlobalDistribution M q f)).app
                (Opposite.op (SimplexCategory.mk k)) t.1 =
              f.app (Opposite.op (SimplexCategory.mk k)) t.1
        have hc : P (nonemptySimplexDimension σ)
            (nonemptySimplexNonDegenerate M σ) := hcanonical
        have hPfun : P m ≍ P (nonemptySimplexDimension σ) :=
          (congr_arg_heq P hdim).symm
        have hz0 :=
          @eqRec_heq ℕ
            (fun k => (orderedComplexSSet M).nonDegenerate k)
            (nonemptySimplexDimension σ) m hdim
            (nonemptySimplexNonDegenerate M σ)
        have hz :
            (hdim ▸ nonemptySimplexNonDegenerate M σ) ≍
              nonemptySimplexNonDegenerate M σ := hz0
        have hprop :
            P m (hdim ▸ nonemptySimplexNonDegenerate M σ) =
              P (nonemptySimplexDimension σ)
                (nonemptySimplexNonDegenerate M σ) :=
          congr_heq hPfun hz
        have hc' : P m
            (hdim ▸ nonemptySimplexNonDegenerate M σ) :=
          Eq.mp hprop.symm hc
        rw [hy] at hc'
        exact hc'
      calc
        _ = (underlyingSSet
              (reducedFree (L (AddCommGrpCat.of G) (q + 1)))).map θ.op
              ((globalCochainRestrictionMap M q
                (nativeMapGlobalDistribution M q f)).app
                  (Opposite.op (SimplexCategory.mk m)) y.1) := by
            exact underlyingSSetMap_naturality_apply
              (globalCochainRestrictionMap M q
                (nativeMapGlobalDistribution M q f)) θ.op y.1
        _ = (underlyingSSet
              (reducedFree (L (AddCommGrpCat.of G) (q + 1)))).map θ.op
              (f.app (Opposite.op (SimplexCategory.mk m)) y.1) := by
            rw [htop]
        _ = _ := (underlyingSSetMap_naturality_apply f θ.op y.1).symm

/-- The glued distribution attached to a map killed by `d_*` satisfies the
facetwise physical compatibility condition. -/
theorem nativeMapGlobalDistribution_fCompatible
    (f : MapsKilledByD (orderedComplexSSet M)
      (AddCommGrpCat.of G) (q + 1)) :
    nativeMapGlobalDistribution M q f.1 ∈
      fCompatibleRedDist (facetRestrictionData (G := G) M q) := by
  change mapRedDist (coboundaryToRange (G := G) M q)
      (nativeMapGlobalDistribution M q f.1) ∈
    physicalInvariantDistributions
      (facetRestrictionData (G := G) M q)
  rw [physicalInvariantDistributions, Submodule.mem_iInf]
  intro σ
  rw [LinearMap.mem_ker]
  calc
    restrictPhysicalRedDist
          (facetRestrictionData (G := G) M q) σ
          (mapRedDist (coboundaryToRange (G := G) M q)
            (nativeMapGlobalDistribution M q f.1)) =
        mapRedDist
          (localCoboundary (G := G) M q σ).toAddMonoidHom
          (mapRedDist (restrictCochain (G := G) M q σ)
            (nativeMapGlobalDistribution M q f.1)) := by
      exact LinearMap.congr_fun
        (restrictPhysicalRedDist_mapRedDist
          (facetRestrictionData (G := G) M q) σ)
        (nativeMapGlobalDistribution M q f.1)
    _ = mapRedDist
          (localCoboundary (G := G) M q σ).toAddMonoidHom
          (nativeMapLocalDistribution M q f.1 σ) := by
      rw [nativeMapGlobalDistribution_restriction]
    _ = 0 :=
      mapRedDist_localCoboundary_nativeMapLocalDistribution_eq_zero
        M q f σ

/-- The compatible global representative obtained by gluing the local
distributions classified by a native killed map. -/
def nativeMapFCompatibleDistribution
    (f : MapsKilledByD (orderedComplexSSet M)
      (AddCommGrpCat.of G) (q + 1)) :
    fCompatibleRedDist (facetRestrictionData (G := G) M q) :=
  ⟨nativeMapGlobalDistribution M q f.1,
    nativeMapGlobalDistribution_fCompatible M q f⟩

/-- Every genuine map into `reducedFree L` killed by `d_*` is the global
cochain evaluation of a compatible reduced distribution. -/
theorem fCompatible_globalRestriction_surjective :
    ∀ f : MapsKilledByD (orderedComplexSSet M)
      (AddCommGrpCat.of G) (q + 1),
      ∃ u : fCompatibleRedDist
          (facetRestrictionData (G := G) M q),
        globalCochainRestrictionMap M q
            (u : RedDist (Cochain M q G)) = f.1 := by
  intro f
  refine ⟨nativeMapFCompatibleDistribution M q f, ?_⟩
  exact nativeMapGlobalRestriction_eq M q f.1

/-- The unconditional geometric input for the strict-section/native-fibre
equivalence. -/
theorem strictFSectionsNativeInput :
    StrictFSectionsNativeInput (G := G) M q where
  killed := fCompatible_globalRestriction_killed M q
  kernel := fCompatible_globalRestriction_kernel M q
  surjective := fCompatible_globalRestriction_surjective M q

/-- Strict compatible sections are unconditionally linearly equivalent to
genuine simplicial maps into the standard Dold--Kan fibre. -/
def strictFSectionsLinearEquivNativeFiberMaps :
    StrictFSections (facetRestrictionData (G := G) M q) ≃ₗ[ℤ]
      (orderedComplexSSet M ⟶
        underlyingSSet (F (AddCommGrpCat.of G) (q + 1))) :=
  (strictFSectionsAddEquivNativeFiberMaps M q
    (strictFSectionsNativeInput (G := G) M q)).toIntLinearEquiv

end GeneralSphereT.SimplicialCochain
