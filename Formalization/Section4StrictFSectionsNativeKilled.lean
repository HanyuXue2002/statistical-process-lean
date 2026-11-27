import Formalization.Section4CochainMapNaturality
import Formalization.Section4StrictFSectionsNativeEquiv
import Formalization.Section4StandardSimplexConstructionCompatibility

set_option linter.style.header false
set_option backward.isDefEq.respectTransparency false

/-!
# Section 4: compatible representatives are killed by the native coboundary

This file proves the first geometric input in
`StrictFSectionsNativeInput`.  Evaluation of a global coboundary on a
nondegenerate simplex depends only on its restriction to the support of that
simplex.  The defining local-zero condition of `fCompatibleRedDist` therefore
forces the reduced-free coboundary of the genuine global restriction map to
vanish.  Degenerate simplices follow from simplicial naturality.
-/

noncomputable section

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits Opposite Simplicial

namespace GeneralSphereT.SimplicialCochain

open GeneralSphereT.PathAlgebra
open GeneralSphereT.PathAlgebra.FacetRestrictionData
open GeneralSphereT.Section4
open GeneralSphereT.StandardModels

universe u

variable {V G : Type u} [LinearOrder V] [Fintype V] [AddCommGroup G]

/-- The support of a nondegenerate ordered simplex, regarded as one of the
facets in the all-simplex restriction presentation. -/
def nonDegenerateSimplexFacet
    (M : AbstractSimplicialComplex V) {n : ℕ}
    (x : (orderedComplexSSet M).nonDegenerate n) : NonemptySimplex M :=
  ⟨orderedSimplexSupport x.1.1, x.1.2⟩

/-- The full simplex on the vertices occurring in a chosen nondegenerate
simplex.  Using the vertex subtype keeps this construction in the same
universe as the ambient complex. -/
abbrev nonDegenerateSimplexSupportComplex
    (M : AbstractSimplicialComplex V) {n : ℕ}
    (x : (orderedComplexSSet M).nonDegenerate n) :
    AbstractSimplicialComplex
      {v : V // v ∈ (nonDegenerateSimplexFacet M x).1} :=
  ⊤

/-- Inclusion of the full support simplex into the ambient complex. -/
def nonDegenerateSimplexSupportMap
    (M : AbstractSimplicialComplex V) {n : ℕ}
    (x : (orderedComplexSSet M).nonDegenerate n) :
    OrderedSimplicialMap
      (nonDegenerateSimplexSupportComplex M x) M where
  toOrderEmbedding := OrderEmbedding.subtype _
  map_mem := by
    intro s hs
    apply (M.isRelLowerSet_faces x.1.2).2
    · intro v hv
      rcases Finset.mem_map.mp hv with ⟨i, hi, rfl⟩
      exact i.2
    · exact Finset.map_nonempty.mpr
        ((nonDegenerateSimplexSupportComplex M x).isRelLowerSet_faces hs).1

@[simp]
theorem nonDegenerateSimplexSupportMap_apply
    (M : AbstractSimplicialComplex V) {n : ℕ}
    (x : (orderedComplexSSet M).nonDegenerate n)
    (v : {v : V // v ∈ (nonDegenerateSimplexFacet M x).1}) :
    nonDegenerateSimplexSupportMap M x v = v.1 :=
  rfl

/-- The chosen simplex, with its vertices regarded as elements of its
support subtype. -/
def nonDegenerateSimplexSupportTop
    (M : AbstractSimplicialComplex V) {n : ℕ}
    (x : (orderedComplexSSet M).nonDegenerate n) :
    (orderedComplexSSet
      (nonDegenerateSimplexSupportComplex M x)).obj
        (Opposite.op (SimplexCategory.mk n)) :=
  ⟨⟨fun i => ⟨x.1.1 i,
        (mem_orderedSimplexSupport x.1.1 (x.1.1 i)).2 ⟨i, rfl⟩⟩,
      fun _ _ h => x.1.1.monotone h⟩, by
    change (orderedSimplexSupport
      (⟨fun i => ⟨x.1.1 i,
        (mem_orderedSimplexSupport x.1.1 (x.1.1 i)).2 ⟨i, rfl⟩⟩,
      fun _ _ h => x.1.1.monotone h⟩ :
        Fin (n + 1) →o
          {v : V // v ∈ (nonDegenerateSimplexFacet M x).1})).Nonempty
    exact Finset.image_nonempty.mpr Finset.univ_nonempty⟩

/-- The support inclusion sends its canonical top simplex back to the
chosen nondegenerate simplex. -/
@[simp]
theorem nonDegenerateSimplexSupportMap_top
    (M : AbstractSimplicialComplex V) {n : ℕ}
    (x : (orderedComplexSSet M).nonDegenerate n) :
    (nonDegenerateSimplexSupportMap M x).toSSetMap.app
        (Opposite.op (SimplexCategory.mk n))
          (nonDegenerateSimplexSupportTop M x) = x.1 := by
  apply Subtype.ext
  apply OrderHom.ext
  funext i
  rfl

/-- Send a cochain on the support of a nondegenerate simplex to the
corresponding cochain on the standard simplex. -/
def localCochainToStandard
    (M : AbstractSimplicialComplex V) {n : ℕ}
    (x : (orderedComplexSSet M).nonDegenerate n) (r : ℕ) :
    Configuration (facesIn M r (nonDegenerateSimplexFacet M x)) G →
      Cochain (nonDegenerateSimplexSupportComplex M x) r G :=
  fun a => Finsupp.equivFunOnFinite.symm fun τ =>
    a ⟨(nonDegenerateSimplexSupportMap M x).mapSimplex τ, by
      intro v hv
      rcases Finset.mem_map.mp hv with ⟨i, hi, rfl⟩
      exact i.2⟩

/-- Pulling back a global cochain is the same as first restricting it to the
support and then identifying that support with the standard simplex. -/
theorem localCochainToStandard_restrictCochain
    (M : AbstractSimplicialComplex V) {n : ℕ}
    (x : (orderedComplexSSet M).nonDegenerate n) (r : ℕ)
    (c : Cochain M r G) :
    localCochainToStandard M x r
      (restrictCochain M r (nonDegenerateSimplexFacet M x) c) =
      (nonDegenerateSimplexSupportMap M x).pullback r c := by
  ext τ
  rfl

/-- Every physical configuration in the paper is a cocycle, because it lies
in the range of a coboundary. -/
theorem coboundaryGroup_cocycle
    (M : AbstractSimplicialComplex V) (q : ℕ)
    (b : CoboundaryGroup (G := G) M q) :
    coboundary M (q + 1) b.1 = 0 := by
  rcases b.2 with ⟨c, hc⟩
  rw [← hc]
  exact coboundary_coboundary M q c

/-- The closedness witness carried by `cocycleToKMap` is proof-irrelevant. -/
theorem cocycleToKMap_congr
    (M : AbstractSimplicialComplex V) (r : ℕ)
    (c c' : Cochain M r G) (hc : coboundary M r c = 0)
    (hc' : coboundary M r c' = 0) (hcc' : c = c') :
    cocycleToKMap M r c hc = cocycleToKMap M r c' hc' := by
  subst c'
  rfl

/-- Evaluate the genuine `K(G,q+1)`-valued map represented by a physical
coboundary at one simplex. -/
def globalCoboundaryKValue
    (M : AbstractSimplicialComplex V) (q : ℕ)
    (Δ : SimplexCategoryᵒᵖ) (x : (orderedComplexSSet M).obj Δ) :
    CoboundaryGroup (G := G) M q →
      (K (AddCommGrpCat.of G) (q + 1)).obj Δ :=
  fun b => (cocycleToKMap M (q + 1) b.1
    (coboundaryGroup_cocycle M q b)).app Δ x

/-- Evaluation on a nondegenerate simplex depends only on the restriction of
the physical coboundary to its support. -/
theorem globalCoboundaryKValue_eq_of_restrict_eq
    (M : AbstractSimplicialComplex V) (q n : ℕ)
    (x : (orderedComplexSSet M).nonDegenerate n)
    (b b' : CoboundaryGroup (G := G) M q)
    (hbb' : restrictCoboundary M q (nonDegenerateSimplexFacet M x) b =
      restrictCoboundary M q (nonDegenerateSimplexFacet M x) b') :
    globalCoboundaryKValue M q (Opposite.op (SimplexCategory.mk n)) x.1 b =
      globalCoboundaryKValue M q (Opposite.op (SimplexCategory.mk n)) x.1 b' := by
  let F := nonDegenerateSimplexSupportMap M x
  have hpull : F.pullback (q + 1) b.1 = F.pullback (q + 1) b'.1 := by
    rw [← localCochainToStandard_restrictCochain M x (q + 1) b.1,
      ← localCochainToStandard_restrictCochain M x (q + 1) b'.1]
    exact congrArg (localCochainToStandard M x (q + 1)) hbb'
  have hb := ConcreteCategory.congr_hom
    (NatTrans.congr_app
      (cocycleToKMap_pullback F (q + 1) b.1
        (coboundaryGroup_cocycle M q b))
      (Opposite.op (SimplexCategory.mk n)))
        (nonDegenerateSimplexSupportTop M x)
  have hb' := ConcreteCategory.congr_hom
    (NatTrans.congr_app
      (cocycleToKMap_pullback F (q + 1) b'.1
        (coboundaryGroup_cocycle M q b'))
      (Opposite.op (SimplexCategory.mk n)))
        (nonDegenerateSimplexSupportTop M x)
  change globalCoboundaryKValue M q _ x.1 b =
      (cocycleToKMap (nonDegenerateSimplexSupportComplex M x) (q + 1)
        (F.pullback (q + 1) b.1) _).app _
          (nonDegenerateSimplexSupportTop M x) at hb
  change globalCoboundaryKValue M q _ x.1 b' =
      (cocycleToKMap (nonDegenerateSimplexSupportComplex M x) (q + 1)
        (F.pullback (q + 1) b'.1) _).app _
          (nonDegenerateSimplexSupportTop M x) at hb'
  calc
    _ = (cocycleToKMap (nonDegenerateSimplexSupportComplex M x) (q + 1)
        (F.pullback (q + 1) b.1) _).app _
          (nonDegenerateSimplexSupportTop M x) := hb
    _ = (cocycleToKMap (nonDegenerateSimplexSupportComplex M x) (q + 1)
        (F.pullback (q + 1) b'.1) _).app _
          (nonDegenerateSimplexSupportTop M x) := by
      have hmap := cocycleToKMap_congr
        (nonDegenerateSimplexSupportComplex M x) (q + 1)
        (F.pullback (q + 1) b.1) (F.pullback (q + 1) b'.1)
        (by
          have hcomm :
              F.pullback (q + 2) (coboundary M (q + 1) b.1) =
                coboundary (nonDegenerateSimplexSupportComplex M x) (q + 1)
                  (F.pullback (q + 1) b.1) := by
            simpa only [LinearMap.comp_apply] using
              DFunLike.congr_fun (F.pullback_coboundary (q + 1)) b.1
          rw [← hcomm, coboundaryGroup_cocycle]
          simp)
        (by
          have hcomm :
              F.pullback (q + 2) (coboundary M (q + 1) b'.1) =
                coboundary (nonDegenerateSimplexSupportComplex M x) (q + 1)
                  (F.pullback (q + 1) b'.1) := by
            simpa only [LinearMap.comp_apply] using
              DFunLike.congr_fun (F.pullback_coboundary (q + 1)) b'.1
          rw [← hcomm, coboundaryGroup_cocycle]
          simp) hpull
      rw [hmap]
    _ = _ := hb'.symm

/-- A set-theoretic factor of physical evaluation through restriction to the
support.  Its values outside the image of restriction are immaterial. -/
def localCoboundaryKValue
    (M : AbstractSimplicialComplex V) (q n : ℕ)
    (x : (orderedComplexSSet M).nonDegenerate n) :
    Configuration
        (facesIn M (q + 1) (nonDegenerateSimplexFacet M x)) G →
      (K (AddCommGrpCat.of G) (q + 1)).obj
        (Opposite.op (SimplexCategory.mk n)) :=
  by
    classical
    exact fun a => if h : ∃ b : CoboundaryGroup (G := G) M q,
        restrictCoboundary M q (nonDegenerateSimplexFacet M x) b = a then
      globalCoboundaryKValue M q _ x.1 (Classical.choose h)
    else 0

theorem localCoboundaryKValue_restrict
    (M : AbstractSimplicialComplex V) (q n : ℕ)
    (x : (orderedComplexSSet M).nonDegenerate n)
    (b : CoboundaryGroup (G := G) M q) :
    localCoboundaryKValue M q n x
        (restrictCoboundary M q (nonDegenerateSimplexFacet M x) b) =
      globalCoboundaryKValue M q _ x.1 b := by
  rw [localCoboundaryKValue, dif_pos ⟨b, rfl⟩]
  apply globalCoboundaryKValue_eq_of_restrict_eq M q n x
  exact (Classical.choose_spec
    (show ∃ b' : CoboundaryGroup (G := G) M q,
      restrictCoboundary M q (nonDegenerateSimplexFacet M x) b' =
        restrictCoboundary M q (nonDegenerateSimplexFacet M x) b from
      ⟨b, rfl⟩))

/-- The value of `d` on the `L`-simplex represented by a primitive is the
`K`-simplex represented by its physical coboundary. -/
theorem d_cochainLValue_eq_globalCoboundaryKValue
    (M : AbstractSimplicialComplex V) (q : ℕ)
    (Δ : SimplexCategoryᵒᵖ) (x : (orderedComplexSSet M).obj Δ)
    (c : Cochain M q G) :
    (d (AddCommGrpCat.of G) (q + 1)).app Δ
        (cochainLValue M q Δ x c) =
      globalCoboundaryKValue M q Δ x (coboundaryToRange M q c) := by
  change (d (AddCommGrpCat.of G) (q + 1)).app Δ
      ((cochainToLMap M q c).app Δ x) =
    (cocycleToKMap M (q + 1) (coboundary M q c) _).app Δ x
  exact cochainToLMap_comp_d_apply M q c Δ x

/-- On a nondegenerate simplex, the local-zero condition in
`fCompatibleRedDist` kills the pointwise reduced-free coboundary. -/
theorem fCompatible_globalRestriction_killed_nonDegenerate
    (M : AbstractSimplicialComplex V) (q n : ℕ)
    (u : fCompatibleRedDist (facetRestrictionData (G := G) M q))
    (x : (orderedComplexSSet M).nonDegenerate n) :
    (reducedFreeMap (d (AddCommGrpCat.of G) (q + 1))).app
        (Opposite.op (SimplexCategory.mk n))
        ((globalCochainRestrictionMap M q
          (u : RedDist (Cochain M q G))).app
            (Opposite.op (SimplexCategory.mk n)) x.1) = 0 := by
  let σ := nonDegenerateSimplexFacet M x
  have hphysical :
      mapRedDist (coboundaryToRange (G := G) M q)
          (u : RedDist (Cochain M q G)) ∈
        physicalInvariantDistributions
          (facetRestrictionData (G := G) M q) :=
    u.property
  rw [physicalInvariantDistributions, Submodule.mem_iInf] at hphysical
  have hlocal := LinearMap.mem_ker.mp (hphysical σ)
  change mapRedDist (restrictCoboundary (G := G) M q σ)
      (mapRedDist (coboundaryToRange (G := G) M q)
        (u : RedDist (Cochain M q G))) = 0 at hlocal
  have hlocal' :
      mapRedDist (restrictCoboundary (G := G) M q σ)
          (mapRedDistFn (coboundaryToRange (G := G) M q)
            (u : RedDist (Cochain M q G))) = 0 := by
    rw [← mapRedDist_eq_mapRedDistFn]
    exact hlocal
  rw [globalCochainRestrictionMap_app_apply,
    reducedFreeMap_app_apply, mapRedDist_eq_mapRedDistFn,
    mapRedDistFn_comp_apply]
  have hd :
      ((d (AddCommGrpCat.of G) (q + 1)).app
          (Opposite.op (SimplexCategory.mk n)) :
            (L (AddCommGrpCat.of G) (q + 1)).obj _ →
              (K (AddCommGrpCat.of G) (q + 1)).obj _) ∘
        cochainLValue M q _ x.1 =
      globalCoboundaryKValue M q _ x.1 ∘
        coboundaryToRange M q := by
    funext c
    exact d_cochainLValue_eq_globalCoboundaryKValue M q _ x.1 c
  rw [hd, ← mapRedDistFn_comp_apply]
  have hfactor :
      globalCoboundaryKValue M q _ x.1 =
        localCoboundaryKValue M q n x ∘
          restrictCoboundary (G := G) M q σ := by
    funext b
    exact (localCoboundaryKValue_restrict M q n x b).symm
  rw [hfactor, ← mapRedDistFn_comp_apply,
    ← mapRedDist_eq_mapRedDistFn, hlocal']
  exact map_zero _

/-- Every compatible global representative gives a genuine `L`-valued map
killed by the native reduced-free coboundary. -/
theorem fCompatible_globalRestriction_killed
    (M : AbstractSimplicialComplex V) (q : ℕ)
    (u : fCompatibleRedDist (facetRestrictionData (G := G) M q)) :
    postcomposeReducedFreeD (orderedComplexSSet M)
        (AddCommGrpCat.of G) (q + 1)
        (globalCochainRestrictionMap M q
          (u : RedDist (Cochain M q G))) = 0 := by
  ext Δ z
  induction Δ using Opposite.rec with
  | _ Δ =>
    induction Δ using SimplexCategory.rec with
    | _ n =>
      change
        (postcomposeReducedFreeD (orderedComplexSSet M)
          (AddCommGrpCat.of G) (q + 1)
          (globalCochainRestrictionMap M q
            (u : RedDist (Cochain M q G)))).app
              (Opposite.op (SimplexCategory.mk n)) z = 0
      obtain ⟨m, f, _, y, hz⟩ :=
        (orderedComplexSSet M).exists_nonDegenerate z
      rw [hz]
      have hy :=
        fCompatible_globalRestriction_killed_nonDegenerate M q m u y
      change
        (postcomposeReducedFreeD (orderedComplexSSet M)
          (AddCommGrpCat.of G) (q + 1)
          (globalCochainRestrictionMap M q
            (u : RedDist (Cochain M q G)))).app
              (Opposite.op (SimplexCategory.mk m)) y.1 = 0 at hy
      calc
        _ = (underlyingSSet
              (reducedFree (K (AddCommGrpCat.of G) (q + 1)))).map f.op
              ((postcomposeReducedFreeD (orderedComplexSSet M)
                (AddCommGrpCat.of G) (q + 1)
                (globalCochainRestrictionMap M q
                  (u : RedDist (Cochain M q G)))).app
                    (Opposite.op (SimplexCategory.mk m)) y.1) := by
            exact underlyingSSetMap_naturality_apply
              (postcomposeReducedFreeD (orderedComplexSSet M)
                (AddCommGrpCat.of G) (q + 1)
                (globalCochainRestrictionMap M q
                  (u : RedDist (Cochain M q G)))) f.op y.1
        _ = 0 := by
          rw [hy]
          change (reducedFree (K (AddCommGrpCat.of G) (q + 1))).map f.op 0 = 0
          exact map_zero _

end GeneralSphereT.SimplicialCochain
