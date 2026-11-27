import Formalization.Section3LiteralConeVanishing
import Formalization.Section4ConeCriterion
import Formalization.Section4SimplicialBasepointLift
import Formalization.SimplicialCochainPullback
import Formalization.SimplicialMaximalFacetPresentation

set_option linter.style.header false

/-!
# Section 4: restriction from the literal cone to its bottom

This file wires the abstract cone criterion to the finite ordered simplicial
cochain model.  First we add the functoriality of `Rprim` and
`StrictFSections` under a compatible facet morphism.  We then specialize it
to the bottom inclusion `M -> simplicialCone M`.

The only relative-cohomology input left explicit is a pointed linear section
of the resulting restriction map on primitive relations.  All other fields
of `Section4.ConeCriterionData`, as well as cone exactness and cone
vanishing, are constructed here.
-/

noncomputable section

namespace GeneralSphereT.PathAlgebra

open FacetRestrictionData

namespace FacetRestrictionHom

section StrictSectionFunctoriality

variable {C₁ B₁ C₂ B₂ : Type*}
variable [AddCommGroup C₁] [AddCommGroup B₁]
variable [AddCommGroup C₂] [AddCommGroup B₂]
variable {Facet₁ Facet₂ : Type*}
variable {CAt₁ : Facet₁ → Type*} {BAt₁ : Facet₁ → Type*}
variable {CAt₂ : Facet₂ → Type*} {BAt₂ : Facet₂ → Type*}
variable [∀ ρ, AddCommGroup (CAt₁ ρ)] [∀ ρ, AddCommGroup (BAt₁ ρ)]
variable [∀ ρ, AddCommGroup (CAt₂ ρ)] [∀ ρ, AddCommGroup (BAt₂ ρ)]
variable {d₁ : C₁ →+ B₁} {d₂ : C₂ →+ B₂}

variable {L₁ : FacetRestrictionData
  (CAt := CAt₁) (BAt := BAt₁) (Facet := Facet₁) d₁}
variable {L₂ : FacetRestrictionData
  (CAt := CAt₂) (BAt := BAt₂) (Facet := Facet₂) d₂}

/-- A compatible facet morphism sends primitive relations to primitive
relations. -/
def mapRprim (F : FacetRestrictionHom L₁ L₂) :
    Rprim (d := d₁) →ₗ[ℤ] Rprim (d := d₂) :=
  LinearMap.codRestrict (Rprim (d := d₂))
    ((mapRedDist F.primitiveMap).comp (Rprim (d := d₁)).subtype) fun r => by
      change mapRedDist d₂ (mapRedDist F.primitiveMap (r : RedDist C₁)) = 0
      calc
        mapRedDist d₂ (mapRedDist F.primitiveMap (r : RedDist C₁)) =
            mapRedDist (d₂.comp F.primitiveMap) (r : RedDist C₁) :=
          mapRedDist_comp_apply F.primitiveMap d₂ (r : RedDist C₁)
        _ = mapRedDist (F.physicalMap.comp d₁) (r : RedDist C₁) := by
          rw [F.commutes]
        _ = mapRedDist F.physicalMap
              (mapRedDist d₁ (r : RedDist C₁)) := by
          symm
          exact mapRedDist_comp_apply d₁ F.physicalMap (r : RedDist C₁)
        _ = 0 := by rw [LinearMap.mem_ker.mp r.property]; simp

@[simp]
theorem mapRprim_coe (F : FacetRestrictionHom L₁ L₂)
    (r : Rprim (d := d₁)) :
    ((mapRprim F r : Rprim (d := d₂)) : RedDist C₂) =
      mapRedDist F.primitiveMap (r : RedDist C₁) :=
  rfl

/-- Physical locally-zero reduced distributions are functorial under a
compatible facet morphism. -/
theorem mapRedDist_mem_physicalInvariant
    (F : FacetRestrictionHom L₁ L₂) {z : RedDist B₁}
    (hz : z ∈ physicalInvariantDistributions L₁) :
    mapRedDist F.physicalMap z ∈ physicalInvariantDistributions L₂ := by
  rw [physicalInvariantDistributions, Submodule.mem_iInf]
  intro ρ
  rw [LinearMap.mem_ker]
  have hzρ : L₁.restrictPhysicalRedDist (F.facetMap ρ) z = 0 :=
    LinearMap.mem_ker.mp
      ((Submodule.mem_iInf (fun σ : Facet₁ =>
        LinearMap.ker (L₁.restrictPhysicalRedDist σ))).1 hz (F.facetMap ρ))
  apply Subtype.ext
  change mapDist (L₂.physicalRes ρ) (mapDist F.physicalMap z.1) = 0
  rw [mapDist_comp_apply, F.physicalRes_commutes ρ,
    ← mapDist_comp_apply]
  change mapDist (F.localPhysicalMap ρ)
    ((L₁.restrictPhysicalRedDist (F.facetMap ρ) z :
      RedDist (BAt₁ (F.facetMap ρ))) : Dist _) = 0
  rw [hzρ]
  simp

/-- Pullback of a compatible representative remains compatible. -/
def mapFCompatible (F : FacetRestrictionHom L₁ L₂) :
    fCompatibleRedDist L₁ →ₗ[ℤ] fCompatibleRedDist L₂ :=
  LinearMap.codRestrict (fCompatibleRedDist L₂)
    ((mapRedDist F.primitiveMap).comp (fCompatibleRedDist L₁).subtype)
      fun u => by
        change mapRedDist d₂
            (mapRedDist F.primitiveMap (u : RedDist C₁)) ∈
          physicalInvariantDistributions L₂
        have hu : mapRedDist d₁ (u : RedDist C₁) ∈
            physicalInvariantDistributions L₁ := u.property
        have himage := mapRedDist_mem_physicalInvariant F hu
        convert himage using 1
        calc
          mapRedDist d₂ (mapRedDist F.primitiveMap (u : RedDist C₁)) =
              mapRedDist (d₂.comp F.primitiveMap) (u : RedDist C₁) :=
            mapRedDist_comp_apply F.primitiveMap d₂ (u : RedDist C₁)
          _ = mapRedDist (F.physicalMap.comp d₁) (u : RedDist C₁) := by
            rw [F.commutes]
          _ = mapRedDist F.physicalMap
                (mapRedDist d₁ (u : RedDist C₁)) := by
            symm
            exact mapRedDist_comp_apply d₁ F.physicalMap (u : RedDist C₁)

@[simp]
theorem mapFCompatible_coe (F : FacetRestrictionHom L₁ L₂)
    (u : fCompatibleRedDist L₁) :
    ((mapFCompatible F u : fCompatibleRedDist L₂) : RedDist C₂) =
      mapRedDist F.primitiveMap (u : RedDist C₁) :=
  rfl

/-- Pullback preserves the locally-zero denominator inside compatible
representatives. -/
theorem mapFCompatible_mem_locallyZero
    (F : FacetRestrictionHom L₁ L₂) {u : fCompatibleRedDist L₁}
    (hu : u ∈ locallyZeroInFCompatible L₁) :
    mapFCompatible F u ∈ locallyZeroInFCompatible L₂ := by
  change mapRedDist F.primitiveMap (u : RedDist C₁) ∈
    locallyZeroRedDist L₂
  exact mapRedDist_mem_locallyZero F hu

/-- The induced pullback on strict compatible sections. -/
def mapStrictFSections (F : FacetRestrictionHom L₁ L₂) :
    StrictFSections L₁ →ₗ[ℤ] StrictFSections L₂ :=
  (locallyZeroInFCompatible L₁).mapQ
    (locallyZeroInFCompatible L₂) (mapFCompatible F)
    (fun _ hu => mapFCompatible_mem_locallyZero F hu)

@[simp]
theorem mapStrictFSections_mkQ (F : FacetRestrictionHom L₁ L₂)
    (u : fCompatibleRedDist L₁) :
    mapStrictFSections F ((locallyZeroInFCompatible L₁).mkQ u) =
      (locallyZeroInFCompatible L₂).mkQ (mapFCompatible F u) := by
  rfl

/-- Naturality of the restriction arrow on strict sections. -/
theorem mapStrictFSections_restrictionClass
    (F : FacetRestrictionHom L₁ L₂) :
    (mapStrictFSections F).comp (restrictionClass L₁) =
      (restrictionClass L₂).comp (mapRprim F) := by
  apply LinearMap.ext
  intro r
  change mapStrictFSections F (restrictionClass L₁ r) =
    restrictionClass L₂ (mapRprim F r)
  rw [restrictionClass_apply, mapStrictFSections_mkQ,
    restrictionClass_apply]
  rfl

/-- The induced map on the primitive kernel attached to one target facet. -/
def mapLocalRprim (F : FacetRestrictionHom L₁ L₂) (ρ : Facet₂) :
    Rprim (d := L₁.localD (F.facetMap ρ)) →ₗ[ℤ]
      Rprim (d := L₂.localD ρ) :=
  LinearMap.codRestrict (Rprim (d := L₂.localD ρ))
    ((mapRedDist (F.localPrimitiveMap ρ)).comp
      (Rprim (d := L₁.localD (F.facetMap ρ))).subtype) fun r => by
        change mapRedDist (L₂.localD ρ)
          (mapRedDist (F.localPrimitiveMap ρ)
            (r : RedDist (CAt₁ (F.facetMap ρ)))) = 0
        calc
          mapRedDist (L₂.localD ρ)
              (mapRedDist (F.localPrimitiveMap ρ)
                (r : RedDist (CAt₁ (F.facetMap ρ)))) =
              mapRedDist ((L₂.localD ρ).comp
                (F.localPrimitiveMap ρ))
                (r : RedDist (CAt₁ (F.facetMap ρ))) :=
            mapRedDist_comp_apply (F.localPrimitiveMap ρ)
              (L₂.localD ρ) (r : RedDist (CAt₁ (F.facetMap ρ)))
          _ = mapRedDist ((F.localPhysicalMap ρ).comp
                (L₁.localD (F.facetMap ρ)))
                (r : RedDist (CAt₁ (F.facetMap ρ))) := by
            rw [F.localD_commutes ρ]
          _ = mapRedDist (F.localPhysicalMap ρ)
                (mapRedDist (L₁.localD (F.facetMap ρ))
                  (r : RedDist (CAt₁ (F.facetMap ρ)))) := by
            symm
            exact mapRedDist_comp_apply (L₁.localD (F.facetMap ρ))
              (F.localPhysicalMap ρ)
              (r : RedDist (CAt₁ (F.facetMap ρ)))
          _ = 0 := by rw [LinearMap.mem_ker.mp r.property]; simp

@[simp]
theorem mapLocalRprim_coe (F : FacetRestrictionHom L₁ L₂)
    (ρ : Facet₂) (r : Rprim (d := L₁.localD (F.facetMap ρ))) :
    ((mapLocalRprim F ρ r : Rprim (d := L₂.localD ρ)) :
      RedDist (CAt₂ ρ)) =
      mapRedDist (F.localPrimitiveMap ρ)
        (r : RedDist (CAt₁ (F.facetMap ρ))) :=
  rfl

/-- Facet evaluation of primitive relations commutes with pullback. -/
theorem evalRprim_mapRprim (F : FacetRestrictionHom L₁ L₂)
    (ρ : Facet₂) :
    (evalRprim L₂ ρ).comp (mapRprim F) =
      (mapLocalRprim F ρ).comp (evalRprim L₁ (F.facetMap ρ)) := by
  apply LinearMap.ext
  intro r
  apply Subtype.ext
  change
    mapRedDist (L₂.primitiveRes ρ)
        (mapRedDist F.primitiveMap (r : RedDist C₁)) =
      mapRedDist (F.localPrimitiveMap ρ)
        (mapRedDist (L₁.primitiveRes (F.facetMap ρ))
          (r : RedDist C₁))
  rw [mapRedDist_comp_apply, F.primitiveRes_commutes ρ,
    ← mapRedDist_comp_apply]

/-- Facet evaluation on strict compatible sections also commutes with
pullback. -/
theorem evalStrictFSections_mapStrictFSections
    (F : FacetRestrictionHom L₁ L₂) (ρ : Facet₂) :
    (evalStrictFSections L₂ ρ).comp (mapStrictFSections F) =
      (mapLocalRprim F ρ).comp
        (evalStrictFSections L₁ (F.facetMap ρ)) := by
  apply LinearMap.ext
  intro x
  change evalStrictFSections L₂ ρ (mapStrictFSections F x) =
    mapLocalRprim F ρ (evalStrictFSections L₁ (F.facetMap ρ) x)
  refine Submodule.Quotient.induction_on
    (p := locallyZeroInFCompatible L₁) x ?_
  intro u
  change
    evalStrictFSections L₂ ρ
        (mapStrictFSections F
          ((locallyZeroInFCompatible L₁).mkQ u)) =
      mapLocalRprim F ρ
        (evalStrictFSections L₁ (F.facetMap ρ)
          ((locallyZeroInFCompatible L₁).mkQ u))
  rw [mapStrictFSections_mkQ, evalStrictFSections_mkQ,
    evalStrictFSections_mkQ]
  apply Subtype.ext
  change
    mapRedDist (L₂.primitiveRes ρ)
        (mapRedDist F.primitiveMap (u : RedDist C₁)) =
      mapRedDist (F.localPrimitiveMap ρ)
        (mapRedDist (L₁.primitiveRes (F.facetMap ρ))
          (u : RedDist C₁))
  rw [mapRedDist_comp_apply, F.primitiveRes_commutes ρ,
    ← mapRedDist_comp_apply]

end StrictSectionFunctoriality

end FacetRestrictionHom

end GeneralSphereT.PathAlgebra

namespace GeneralSphereT.SimplicialCochain

open GeneralSphereT.PathAlgebra
open GeneralSphereT.PathAlgebra.FacetRestrictionData
open GeneralSphereT.PathAlgebra.FacetRestrictionHom

variable {V G : Type*} [LinearOrder V] [Fintype V] [AddCommGroup G]
variable (M : AbstractSimplicialComplex V)

/- `Option V` has low-level generic relation instances in core.  Override
both relations, not only the bundled order, so the literal cone uses exactly
the `WithBot` order from Section 3. -/
local instance (priority := 10000) section4ConeOptionLE : LE (Option V) :=
  @WithBot.instLE V inferInstance

local instance (priority := 10000) section4ConeOptionLT : LT (Option V) :=
  @WithBot.instLT V inferInstance

local instance (priority := 10000) section4ConeOptionLinearOrder :
    LinearOrder (Option V) :=
  @WithBot.linearOrder V inferInstance

/-- The order embedding of the bottom vertices into the literal cone. -/
def coneBottomOrderEmbedding : V ↪o Option V :=
  OrderEmbedding.ofStrictMono (fun v : V => some v) (by
    intro v w hvw
    exact WithBot.LT.coe_lt_coe hvw)

omit [Fintype V] in
@[simp]
theorem coneBottomOrderEmbedding_apply (v : V) :
    coneBottomOrderEmbedding v = some v :=
  rfl

/-- The bottom inclusion as an ordered simplicial map. -/
def coneBottomInclusion : OrderedSimplicialMap M (simplicialCone M) where
  toOrderEmbedding := coneBottomOrderEmbedding
  map_mem := by
    intro s hs
    have himage : s.map coneBottomOrderEmbedding.toEmbedding =
        s.image some := by
      ext o
      simp
    rw [himage, mem_simplicialCone]
    refine ⟨Finset.image_nonempty.mpr
      ((M.isRelLowerSet_faces hs).1), Or.inr ?_⟩
    have hbase : coneBaseVertices (s.image some) = s := by
      ext v
      rw [mem_coneBaseVertices]
      simp
    rw [hbase]
    exact hs

omit [Fintype V] in
@[simp]
theorem coneBottomInclusion_apply (v : V) :
    coneBottomInclusion M v = some v :=
  rfl

/-- The compatible facet morphism induced contravariantly by bottom
inclusion. -/
def coneBottomFacetHom (n : ℕ) :
    FacetRestrictionHom
      (facetRestrictionData (G := G) (simplicialCone M) n)
      (facetRestrictionData (G := G) M n) :=
  (coneBottomInclusion M).toFacetRestrictionHom (G := G) n

omit [Fintype V] in
/-- The bottom facet over the chosen vertex is carried to the corresponding
singleton facet of the cone. -/
@[simp]
theorem coneBottom_mapFacet_basepoint (b : V) :
    (coneBottomInclusion M).mapFacet (basepointFacet M b) =
      basepointFacet (simplicialCone M) (some b) := by
  apply Subtype.ext
  change ({b} : Finset V).map coneBottomOrderEmbedding.toEmbedding =
    ({some b} : Finset (Option V))
  rw [Finset.map_singleton]
  exact congrArg (fun o : Option V => ({o} : Finset (Option V)))
    (coneBottomOrderEmbedding_apply b)

/-- Pullback of primitive relations from the cone to its bottom. -/
def coneBottomRprimRestriction (n : ℕ) :=
  mapRprim (coneBottomFacetHom (G := G) M n)

/-- Pullback of strict compatible sections from the cone to its bottom. -/
def coneBottomStrictFSectionsRestriction (n : ℕ) :=
  mapStrictFSections (coneBottomFacetHom (G := G) M n)

/-! ## The pointed cone condition -/

/-- The whole cone on the chosen basepoint: the edge from the apex to the
bottom vertex `b`. -/
def coneBasepointEdgeFacet (b : V) :
    NonemptySimplex (simplicialCone M) :=
  ⟨insert none (basepointFacet (simplicialCone M) (some b)).1,
    simplicialCone_isConeAt M
      (basepointFacet (simplicialCone M) (some b))⟩

omit [Fintype V] in
/-- The bottom basepoint vertex is a face of its cone edge. -/
theorem basepointFacet_subset_coneBasepointEdgeFacet (b : V) :
    (basepointFacet (simplicialCone M) (some b)).1 ⊆
      (coneBasepointEdgeFacet M b).1 :=
  Finset.subset_insert none _

/-- Vanishing after restriction to the basepoint edge implies vanishing at
its bottom endpoint. -/
theorem restrictRedDist_basepoint_eq_zero_of_edge_eq_zero
    (b : V) (n : ℕ)
    (u : RedDist (Cochain (simplicialCone M) n G))
    (hedge :
      (facetRestrictionData (G := G) (simplicialCone M) n).restrictRedDist
        (coneBasepointEdgeFacet M b) u = 0) :
    (facetRestrictionData (G := G) (simplicialCone M) n).restrictRedDist
        (basepointFacet (simplicialCone M) (some b)) u = 0 := by
  let S := facesIn (simplicialCone M) n
    (basepointFacet (simplicialCone M) (some b))
  let T := facesIn (simplicialCone M) n (coneBasepointEdgeFacet M b)
  have hST : S ⊆ T := by
    intro η hη
    exact hη.trans (basepointFacet_subset_coneBasepointEdgeFacet M b)
  change mapRedDist (coordinateRestriction S) u = 0
  change mapRedDist (coordinateRestriction T) u = 0 at hedge
  let q : Configuration T G →+ Configuration S G :=
    configurationRestrictionOfSubset (G := G) hST
  calc
    mapRedDist (coordinateRestriction S) u =
        mapRedDist (q.comp (coordinateRestriction T)) u := by
      rw [configurationRestrictionOfSubset_comp_coordinateRestriction]
    _ = mapRedDist q (mapRedDist (coordinateRestriction T) u) := by
      symm
      exact mapRedDist_comp_apply (coordinateRestriction T) q u
    _ = 0 := by rw [hedge]; simp

/-- A primitive relation which vanishes on the basepoint edge also vanishes
at the bottom basepoint vertex. -/
theorem evalRprim_basepoint_eq_zero_of_edge_eq_zero
    (b : V) (n : ℕ)
    (r : Rprim (d := coboundaryToRange (G := G) (simplicialCone M) n))
    (hedge : evalRprim
      (facetRestrictionData (G := G) (simplicialCone M) n)
      (coneBasepointEdgeFacet M b) r = 0) :
    evalRprim (facetRestrictionData (G := G) (simplicialCone M) n)
      (basepointFacet (simplicialCone M) (some b)) r = 0 := by
  apply Subtype.ext
  apply restrictRedDist_basepoint_eq_zero_of_edge_eq_zero
    (G := G) M b n (r : RedDist _)
  exact congrArg Subtype.val hedge

/-- The same edge-to-endpoint implication for strict compatible sections. -/
theorem evalStrictFSections_basepoint_eq_zero_of_edge_eq_zero
    (b : V) (n : ℕ) :
    ∀ x : StrictFSections
      (facetRestrictionData (G := G) (simplicialCone M) n),
      evalStrictFSections
          (facetRestrictionData (G := G) (simplicialCone M) n)
          (coneBasepointEdgeFacet M b) x = 0 →
        evalStrictFSections
          (facetRestrictionData (G := G) (simplicialCone M) n)
          (basepointFacet (simplicialCone M) (some b)) x = 0 := by
  intro x
  refine Submodule.Quotient.induction_on
    (p := locallyZeroInFCompatible
      (facetRestrictionData (G := G) (simplicialCone M) n)) x ?_
  intro u hu
  change evalFCompatible
      (facetRestrictionData (G := G) (simplicialCone M) n)
      (coneBasepointEdgeFacet M b) u = 0 at hu
  change evalFCompatible
      (facetRestrictionData (G := G) (simplicialCone M) n)
      (basepointFacet (simplicialCone M) (some b)) u = 0
  apply Subtype.ext
  apply restrictRedDist_basepoint_eq_zero_of_edge_eq_zero
    (G := G) M b n (u : RedDist _)
  exact congrArg Subtype.val hu

/-- Primitive cone relations satisfying the pointed condition on the whole
basepoint edge `C_v{b}`. -/
abbrev ConePointedRelations (b : V) (n : ℕ) :=
  LinearMap.ker
    (evalRprim (facetRestrictionData (G := G) (simplicialCone M) n)
      (coneBasepointEdgeFacet M b))

/-- Strict cone sections satisfying the pointed condition on the whole
basepoint edge `C_v{b}`. -/
abbrev ConePointedSections (b : V) (n : ℕ) :=
  LinearMap.ker
    (evalStrictFSections
      (facetRestrictionData (G := G) (simplicialCone M) n)
      (coneBasepointEdgeFacet M b))

/-- Restriction of pointed cone relations to pointed cone sections. -/
def conePointedRestriction (b : V) (n : ℕ) :
    ConePointedRelations (G := G) M b n →ₗ[ℤ]
      ConePointedSections (G := G) M b n :=
  LinearMap.codRestrict (ConePointedSections (G := G) M b n)
    ((restrictionClass
      (facetRestrictionData (G := G) (simplicialCone M) n)).comp
      (ConePointedRelations (G := G) M b n).subtype) fun r => by
        rw [LinearMap.mem_ker]
        have h := LinearMap.congr_fun
          (evalStrictFSections_comp_restrictionClass
            (facetRestrictionData (G := G) (simplicialCone M) n)
            (coneBasepointEdgeFacet M b)) r.1
        simpa [r.2] using h

@[simp]
theorem conePointedRestriction_coe
    (b : V) (n : ℕ) (r : ConePointedRelations (G := G) M b n) :
    (conePointedRestriction (G := G) M b n r :
      StrictFSections
        (facetRestrictionData (G := G) (simplicialCone M) n)) =
      restrictionClass
        (facetRestrictionData (G := G) (simplicialCone M) n) r :=
  rfl

/-- The cone obstruction restricted to edge-pointed sections. -/
def conePointedObstruction (b : V) (n : ℕ) :
    ConePointedSections (G := G) M b n →ₗ[ℤ]
      Tau
        (fun σ : NonemptySimplex (simplicialCone M) =>
          facesIn (simplicialCone M) n σ)
        (facetRestrictionData (G := G) (simplicialCone M) n) :=
  (simplicialObstruction (G := G) (simplicialCone M) n).comp
    (ConePointedSections (G := G) M b n).subtype

/-- Pullback of an edge-pointed cone relation is a relation based at the
chosen bottom vertex. -/
def coneBottomPointedRelationRestriction (b : V) (n : ℕ) :
    ConePointedRelations (G := G) M b n →ₗ[ℤ]
      LinearMap.ker
        (simplicialBasepointRowData (G := G) M b n).evalR :=
  LinearMap.codRestrict
    (LinearMap.ker (simplicialBasepointRowData (G := G) M b n).evalR)
    ((coneBottomRprimRestriction (G := G) M n).comp
      (ConePointedRelations (G := G) M b n).subtype) fun r => by
        rw [LinearMap.mem_ker]
        have hvertex := evalRprim_basepoint_eq_zero_of_edge_eq_zero
          (G := G) M b n r.1 r.2
        let F := coneBottomFacetHom (G := G) M n
        have hnat := LinearMap.congr_fun
          (evalRprim_mapRprim F (basepointFacet M b)) r.1
        have hfacet : F.facetMap (basepointFacet M b) =
            basepointFacet (simplicialCone M) (some b) := by
          change (coneBottomInclusion M).mapFacet (basepointFacet M b) =
            basepointFacet (simplicialCone M) (some b)
          exact coneBottom_mapFacet_basepoint M b
        have hsource : evalRprim
            (facetRestrictionData (G := G) (simplicialCone M) n)
            (F.facetMap (basepointFacet M b)) r.1 = 0 := by
          rw [hfacet]
          exact hvertex
        change evalRprim
          (facetRestrictionData (G := G) M n) (basepointFacet M b)
          (mapRprim F r.1) = 0
        calc
          evalRprim (facetRestrictionData (G := G) M n)
              (basepointFacet M b) (mapRprim F r.1) =
              mapLocalRprim F (basepointFacet M b)
                (evalRprim
                  (facetRestrictionData (G := G) (simplicialCone M) n)
                  (F.facetMap (basepointFacet M b)) r.1) := by
            simpa [F] using hnat
          _ = 0 := by rw [hsource]; simp

/-- Pullback of an edge-pointed cone section is a section based at the
chosen bottom vertex. -/
def coneBottomPointedSectionRestriction (b : V) (n : ℕ) :
    ConePointedSections (G := G) M b n →ₗ[ℤ]
      LinearMap.ker
        (simplicialBasepointRowData (G := G) M b n).evalM :=
  LinearMap.codRestrict
    (LinearMap.ker (simplicialBasepointRowData (G := G) M b n).evalM)
    ((coneBottomStrictFSectionsRestriction (G := G) M n).comp
      (ConePointedSections (G := G) M b n).subtype) fun x => by
        rw [LinearMap.mem_ker]
        have hvertex :=
          evalStrictFSections_basepoint_eq_zero_of_edge_eq_zero
            (G := G) M b n x.1 x.2
        let F := coneBottomFacetHom (G := G) M n
        have hnat := LinearMap.congr_fun
          (evalStrictFSections_mapStrictFSections F (basepointFacet M b)) x.1
        have hfacet : F.facetMap (basepointFacet M b) =
            basepointFacet (simplicialCone M) (some b) := by
          change (coneBottomInclusion M).mapFacet (basepointFacet M b) =
            basepointFacet (simplicialCone M) (some b)
          exact coneBottom_mapFacet_basepoint M b
        have hsource : evalStrictFSections
            (facetRestrictionData (G := G) (simplicialCone M) n)
            (F.facetMap (basepointFacet M b)) x.1 = 0 := by
          rw [hfacet]
          exact hvertex
        change evalStrictFSections
          (facetRestrictionData (G := G) M n) (basepointFacet M b)
          (mapStrictFSections F x.1) = 0
        calc
          evalStrictFSections (facetRestrictionData (G := G) M n)
              (basepointFacet M b) (mapStrictFSections F x.1) =
              mapLocalRprim F (basepointFacet M b)
                (evalStrictFSections
                  (facetRestrictionData (G := G) (simplicialCone M) n)
                  (F.facetMap (basepointFacet M b)) x.1) := by
            simpa [F] using hnat
          _ = 0 := by rw [hsource]; simp

/-- Naturality of primitive restriction after imposing the two correct
pointed conditions: a vertex on the bottom and its whole cone edge upstairs. -/
theorem coneBottom_pointedRestriction_natural (b : V) (n : ℕ) :
    (coneBottomPointedSectionRestriction (G := G) M b n).comp
        (conePointedRestriction (G := G) M b n) =
      (simplicialBasepointRowData
        (G := G) M b n).basedRestriction.comp
        (coneBottomPointedRelationRestriction (G := G) M b n) := by
  apply LinearMap.ext
  intro r
  apply Subtype.ext
  change mapStrictFSections (coneBottomFacetHom (G := G) M n)
      (restrictionClass
        (facetRestrictionData (G := G) (simplicialCone M) n) r.1) =
    restrictionClass (facetRestrictionData (G := G) M n)
      (mapRprim (coneBottomFacetHom (G := G) M n) r.1)
  exact LinearMap.congr_fun
    (mapStrictFSections_restrictionClass
      (coneBottomFacetHom (G := G) M n)) r.1

/-- Exactness of the cone row survives imposing vanishing on the whole
basepoint edge.  This is the same kernel argument as for the vertex-based
row, now with the mathematically correct cone-pointed evaluation. -/
theorem exact_conePointedRestriction_conePointedObstruction
    (b : V) (n : ℕ) :
    Function.Exact (conePointedRestriction (G := G) M b n)
      (conePointedObstruction (G := G) M b n) := by
  let LC := facetRestrictionData (G := G) (simplicialCone M) n
  let facetsC := fun σ : NonemptySimplex (simplicialCone M) =>
    facesIn (simplicialCone M) n σ
  have hexact : Function.Exact (restrictionClass LC)
      (simplicialObstruction (G := G) (simplicialCone M) n) := by
    exact exact_restrictionClass_obstruction facetsC LC
      (simplicialMapLocallyZero_eq_physicalNonfaceCubeSpan
        (G := G) (simplicialCone M) n)
  intro x
  constructor
  · intro hx
    have hω : simplicialObstruction (G := G) (simplicialCone M) n
        (x : StrictFSections LC) = 0 := hx
    rcases (hexact (x : StrictFSections LC)).mp hω with ⟨r, hr⟩
    have hrPointed : evalRprim LC (coneBasepointEdgeFacet M b) r = 0 := by
      have heval := LinearMap.congr_fun
        (evalStrictFSections_comp_restrictionClass LC
          (coneBasepointEdgeFacet M b)) r
      calc
        evalRprim LC (coneBasepointEdgeFacet M b) r =
            evalStrictFSections LC (coneBasepointEdgeFacet M b)
              (restrictionClass LC r) := by
          simpa using heval.symm
        _ = evalStrictFSections LC (coneBasepointEdgeFacet M b) x := by
          rw [hr]
        _ = 0 := x.2
    refine ⟨⟨r, hrPointed⟩, ?_⟩
    apply Subtype.ext
    exact hr
  · rintro ⟨r, rfl⟩
    change simplicialObstruction (G := G) (simplicialCone M) n
      (restrictionClass LC r) = 0
    exact LinearMap.congr_fun hexact.linearMap_comp_eq_zero r

/-- Since `tau` of the literal cone is zero, every edge-pointed strict cone
section is represented by an edge-pointed primitive relation. -/
theorem conePointedRestriction_surjective (b : V) (n : ℕ) :
    Function.Surjective (conePointedRestriction (G := G) M b n) := by
  intro x
  apply (exact_conePointedRestriction_conePointedObstruction
    (G := G) M b n x).mp
  exact @Subsingleton.elim _
    (literalSimplicialConeTau_subsingleton (G := G) M n)
    (conePointedObstruction (G := G) M b n x) 0

/-! ## The relative extension input and the cone criterion -/

/-- The sole relative-cohomology input needed for (4.6).

The codomain of `extendRelation` is already the kernel of evaluation on the
whole basepoint edge.  Thus the field records, rather than hides, the
condition that the extension vanishes on `C_v{b}`. -/
structure PointedConeRelationExtensionData (b : V) (n : ℕ) where
  extendRelation :
    LinearMap.ker
        (simplicialBasepointRowData (G := G) M b n).evalR →ₗ[ℤ]
      ConePointedRelations (G := G) M b n
  restrict_extend :
    (coneBottomPointedRelationRestriction (G := G) M b n).comp
        extendRelation = LinearMap.id

namespace PointedConeRelationExtensionData

variable {b : V} {n : ℕ}
variable (E : PointedConeRelationExtensionData (G := G) M b n)

/-- All cone-criterion data except relative extension are canonical pullback
maps; the extension and its right-inverse identity are the two fields above. -/
def toConeCriterionData :
    GeneralSphereT.Section4.ConeCriterionData
      (simplicialBasepointRowData
        (G := G) M b n).basedRestriction
      (conePointedRestriction (G := G) M b n) where
  restrictRelation :=
    coneBottomPointedRelationRestriction (G := G) M b n
  restrictMap := coneBottomPointedSectionRestriction (G := G) M b n
  extendRelation := E.extendRelation
  restrict_extend := E.restrict_extend
  restriction_natural := coneBottom_pointedRestriction_natural
    (G := G) M b n

/-- Concrete equation (4.6): restrictions of based primitive relations are
exactly restrictions of edge-pointed maps on the literal cone. -/
theorem range_basedRestriction_eq_coneNullMaps :
    LinearMap.range
        (simplicialBasepointRowData
          (G := G) M b n).basedRestriction =
      E.toConeCriterionData.coneNullMaps :=
  E.toConeCriterionData.range_restriction_eq_coneNullMaps
    (conePointedRestriction_surjective (G := G) M b n)

/-- The concrete comparison `theta` obtained from the literal cone model.
Its target is based strict sections modulo restrictions of edge-pointed cone
sections, exactly the pointed null-map presentation. -/
def thetaFromPointedCone :
    Tau (fun σ : NonemptySimplex M => facesIn M n σ)
        (facetRestrictionData (G := G) M n) ≃ₗ[ℤ]
      GeneralSphereT.Section4.PointedHomotopyClasses
        (LinearMap.ker
          (simplicialBasepointRowData (G := G) M b n).evalM)
        E.toConeCriterionData.coneNullMaps := by
  let LB := facetRestrictionData (G := G) M n
  let facetsB := fun σ : NonemptySimplex M => facesIn M n σ
  have hexact : Function.Exact (restrictionClass LB)
      (simplicialObstruction (G := G) M n) := by
    exact exact_restrictionClass_obstruction facetsB LB
      (simplicialMapLocallyZero_eq_physicalNonfaceCubeSpan
        (G := G) M n)
  have hsurj : Function.Surjective
      (simplicialObstruction (G := G) M n) := by
    exact obstruction_surjective facetsB LB
      (simplicialMapLocallyZero_eq_physicalNonfaceCubeSpan
        (G := G) M n)
      (simplicialMapRedDist_surjective (G := G) M n)
  exact GeneralSphereT.Section4.theta
    (simplicialBasepointRowData (G := G) M b n)
    E.toConeCriterionData.coneNullMaps hexact hsurj
    E.range_basedRestriction_eq_coneNullMaps

end PointedConeRelationExtensionData

end GeneralSphereT.SimplicialCochain
