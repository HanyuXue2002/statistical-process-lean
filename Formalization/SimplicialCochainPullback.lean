import Formalization.SimplicialCoboundarySquare
import Formalization.SimplicialFacetData
import Formalization.PrimitiveQuotientFunctoriality

set_option linter.style.header false

/-!
# Pullback of finite ordered simplicial cochains

This module proves the strict cochain pullback needed for the concrete form of
(2.36) for vertex maps which preserve the ambient order and are injective.
Such a map sends every increasing nondegenerate simplex to an increasing
nondegenerate simplex, so no permutation sign or degenerate-simplex branch is
needed.  Pullback commutes with the ordered coboundary on the nose.

An arbitrary simplicial vertex map requires a larger normalized-simplex API:
the image of a simplex must be sent to zero when vertices collide, and otherwise
must be multiplied by the sign of the permutation which sorts its image.  That
generalization is deliberately not asserted here.
-/

noncomputable section

open scoped BigOperators

namespace GeneralSphereT.SimplicialCochain

universe uV uW uU

variable {V : Type uV} {W : Type uW} {U : Type uU}
variable [LinearOrder V] [LinearOrder W] [LinearOrder U]
variable [Fintype V] [Fintype W] [Fintype U]

/-- An order-preserving injective vertex map which carries simplices to
simplices.  This is the nondegenerate, sign-free case of simplicial pullback. -/
structure OrderedSimplicialMap
    (K : AbstractSimplicialComplex V)
    (L : AbstractSimplicialComplex W) where
  toOrderEmbedding : V ↪o W
  map_mem : ∀ {s : Finset V}, s ∈ K →
    s.map toOrderEmbedding.toEmbedding ∈ L

namespace OrderedSimplicialMap

variable {K : AbstractSimplicialComplex V}
variable {L : AbstractSimplicialComplex W}
variable {M : AbstractSimplicialComplex U}

instance : CoeFun (OrderedSimplicialMap K L) (fun _ => V → W) :=
  ⟨fun F => F.toOrderEmbedding⟩

/-- Identity ordered simplicial map. -/
def id (K : AbstractSimplicialComplex V) : OrderedSimplicialMap K K where
  toOrderEmbedding := OrderEmbedding.id V
  map_mem := by
    intro s hs
    simpa using hs

/-- Composition of ordered simplicial maps. -/
def comp (H : OrderedSimplicialMap L M)
    (F : OrderedSimplicialMap K L) : OrderedSimplicialMap K M where
  toOrderEmbedding := F.toOrderEmbedding.comp H.toOrderEmbedding
  map_mem := by
    intro s hs
    have hF := F.map_mem hs
    have hH := H.map_mem hF
    have himage :
        s.map (F.toOrderEmbedding.comp H.toOrderEmbedding).toEmbedding =
          (s.map F.toOrderEmbedding.toEmbedding).map
            H.toOrderEmbedding.toEmbedding := by
      ext u
      simp
    rw [himage]
    exact hH

/-- The image of a nondegenerate simplex under an ordered simplicial map. -/
def mapSimplex (F : OrderedSimplicialMap K L) {n : ℕ}
    (σ : Simplex K n) : Simplex L n :=
  ⟨σ.1.map F.toOrderEmbedding.toEmbedding,
    F.map_mem σ.2.1,
    by simpa using σ.2.2⟩

omit [Fintype V] [Fintype W] in
@[simp]
theorem mapSimplex_val (F : OrderedSimplicialMap K L) {n : ℕ}
    (σ : Simplex K n) :
    (F.mapSimplex σ).1 = σ.1.map F.toOrderEmbedding.toEmbedding :=
  rfl

omit [Fintype V] in
@[simp]
theorem mapSimplex_id {n : ℕ} (σ : Simplex K n) :
    (id K).mapSimplex σ = σ := by
  apply Subtype.ext
  simp [id, mapSimplex]

omit [Fintype V] [Fintype W] [Fintype U] in
@[simp]
theorem mapSimplex_comp (H : OrderedSimplicialMap L M)
    (F : OrderedSimplicialMap K L) {n : ℕ} (σ : Simplex K n) :
    (comp H F).mapSimplex σ = H.mapSimplex (F.mapSimplex σ) := by
  apply Subtype.ext
  ext u
  simp [comp, mapSimplex]

/-- The order embedding identifies the vertices of a simplex with the vertices
of its image. -/
def vertexEquiv (F : OrderedSimplicialMap K L) (s : Finset V) :
    {v // v ∈ s} ≃ {w // w ∈ s.map F.toOrderEmbedding.toEmbedding} :=
  Finset.equivMap F.toOrderEmbedding.toEmbedding s

omit [Fintype V] [Fintype W] in
/-- Mapping a simplex commutes with deletion of a vertex. -/
theorem mapSimplex_eraseVertex (F : OrderedSimplicialMap K L)
    {n : ℕ} (τ : Simplex K (n + 1)) (v : V) (hv : v ∈ τ.1) :
    F.mapSimplex (eraseVertex K τ v hv) =
      eraseVertex L (F.mapSimplex τ) (F v)
        (Finset.mem_map.mpr ⟨v, hv, rfl⟩) := by
  apply Subtype.ext
  exact Finset.map_erase _ _ _

omit [Fintype V] [Fintype W] in
/-- Strict monotonicity preserves the number of vertices below a chosen
vertex, hence preserves ordered incidence signs. -/
theorem incidenceSign_mapSimplex (F : OrderedSimplicialMap K L)
    {n : ℕ} (τ : Simplex K (n + 1)) (v : V) :
    incidenceSign L (F.mapSimplex τ) (F v) = incidenceSign K τ v := by
  change
    (-1 : ℤ) ^ ((τ.1.map F.toOrderEmbedding.toEmbedding).filter
      (fun w => w < F v)).card =
      (-1 : ℤ) ^ (τ.1.filter fun w => w < v).card
  have hfilter :
      (τ.1.map F.toOrderEmbedding.toEmbedding).filter
          (fun w => w < F v) =
        (τ.1.filter fun w => w < v).map
          F.toOrderEmbedding.toEmbedding := by
    rw [Finset.filter_map]
    congr 1
    ext w
    simp
  rw [hfilter, Finset.card_map]

variable {G : Type*} [AddCommGroup G]

/-- Pullback of ordered cochains, first as an additive map. -/
def pullbackAddHom (F : OrderedSimplicialMap K L) (n : ℕ) :
    Cochain L n G →+ Cochain K n G where
  toFun c := Finsupp.equivFunOnFinite.symm fun σ => c (F.mapSimplex σ)
  map_zero' := by
    ext σ
    simp
  map_add' c c' := by
    ext σ
    simp

/-- Pullback of ordered cochains as a `ℤ`-linear map. -/
def pullback (F : OrderedSimplicialMap K L) (n : ℕ) :
    Cochain L n G →ₗ[ℤ] Cochain K n G :=
  (F.pullbackAddHom n).toIntLinearMap

omit [Fintype W] in
@[simp]
theorem pullback_apply (F : OrderedSimplicialMap K L) (n : ℕ)
    (c : Cochain L n G) (σ : Simplex K n) :
    F.pullback n c σ = c (F.mapSimplex σ) :=
  rfl

/-- Pointwise naturality of the ordered coboundary under an ordered simplicial
map. -/
theorem pullback_coboundary_apply (F : OrderedSimplicialMap K L)
    (n : ℕ) (c : Cochain L n G) (τ : Simplex K (n + 1)) :
    F.pullback (n + 1) (coboundary L n c) τ =
      coboundary K n (F.pullback n c) τ := by
  rw [pullback_apply, coboundary_apply, coboundary_apply]
  symm
  refine Fintype.sum_equiv (F.vertexEquiv τ.1) _ _ ?_
  intro v
  change
    incidenceSign K τ v.1 •
        c (F.mapSimplex (eraseVertex K τ v.1 v.2)) =
      incidenceSign L (F.mapSimplex τ) (F v.1) •
        c (eraseVertex L (F.mapSimplex τ) (F v.1) _)
  rw [F.incidenceSign_mapSimplex]
  rw [F.mapSimplex_eraseVertex]

/-- Ordered simplicial pullback strictly commutes with coboundary. -/
theorem pullback_coboundary (F : OrderedSimplicialMap K L) (n : ℕ) :
    (F.pullback (n + 1)).comp (coboundary (G := G) L n) =
      (coboundary K n).comp (F.pullback n) := by
  apply LinearMap.ext
  intro c
  ext τ
  exact F.pullback_coboundary_apply n c τ

/-- Pullback along the identity map is literally the identity linear map. -/
theorem pullback_id (n : ℕ) :
    (id K).pullback (G := G) n = LinearMap.id := by
  apply LinearMap.ext
  intro c
  ext σ
  simp

omit [Fintype U] in
/-- Pullback is strictly contravariant under composition. -/
theorem pullback_comp (H : OrderedSimplicialMap L M)
    (F : OrderedSimplicialMap K L) (n : ℕ) :
    (comp H F).pullback (G := G) n =
      (F.pullback n).comp (H.pullback n) := by
  apply LinearMap.ext
  intro c
  ext σ
  simp

section FacetRestriction

open GeneralSphereT.PathAlgebra
open GeneralSphereT.PathAlgebra.FacetRestrictionData

/-- The image of a facet under an ordered simplicial map. -/
def mapFacet (F : OrderedSimplicialMap K L)
    (σ : NonemptySimplex K) : NonemptySimplex L :=
  ⟨σ.1.map F.toOrderEmbedding.toEmbedding, F.map_mem σ.2⟩

omit [Fintype V] [Fintype W] in
@[simp]
theorem mapFacet_val (F : OrderedSimplicialMap K L)
    (σ : NonemptySimplex K) :
    (F.mapFacet σ).1 = σ.1.map F.toOrderEmbedding.toEmbedding :=
  rfl

/-- A face of a source facet maps to the corresponding face of its image
facet. -/
def mapFace (F : OrderedSimplicialMap K L) {n : ℕ}
    (σ : NonemptySimplex K) (η : facesIn K n σ) :
    facesIn L n (F.mapFacet σ) :=
  ⟨F.mapSimplex η.1, Finset.map_subset_map.mpr η.2⟩

omit [Fintype V] [Fintype W] in
@[simp]
theorem mapFace_val (F : OrderedSimplicialMap K L) {n : ℕ}
    (σ : NonemptySimplex K) (η : facesIn K n σ) :
    (F.mapFace σ η).1 = F.mapSimplex η.1 :=
  rfl

omit [Fintype V] [Fintype W] in
/-- Mapping a local face commutes with deleting a vertex. -/
theorem mapFace_eraseVertexIn (F : OrderedSimplicialMap K L)
    {n : ℕ} (σ : NonemptySimplex K) (τ : facesIn K (n + 1) σ)
    (v : V) (hv : v ∈ τ.1.1) :
    F.mapFace σ (eraseVertexIn K σ τ v hv) =
      eraseVertexIn L (F.mapFacet σ) (F.mapFace σ τ) (F v)
        (Finset.mem_map.mpr ⟨v, hv, rfl⟩) := by
  apply Subtype.ext
  exact F.mapSimplex_eraseVertex τ.1 v hv

/-- Pullback on the cochains supported in one facet. -/
def localPullbackAddHom (F : OrderedSimplicialMap K L) (n : ℕ)
    (σ : NonemptySimplex K) :
    Configuration (facesIn L n (F.mapFacet σ)) G →+
      Configuration (facesIn K n σ) G where
  toFun c := Finsupp.equivFunOnFinite.symm fun η => c (F.mapFace σ η)
  map_zero' := by
    ext η
    simp
  map_add' c c' := by
    ext η
    simp

omit [Fintype W] in
@[simp]
theorem localPullbackAddHom_apply (F : OrderedSimplicialMap K L)
    (n : ℕ) (σ : NonemptySimplex K)
    (c : Configuration (facesIn L n (F.mapFacet σ)) G)
    (η : facesIn K n σ) :
    F.localPullbackAddHom n σ c η = c (F.mapFace σ η) :=
  rfl

/-- Local pullback also commutes strictly with the local coboundary. -/
theorem localPullback_coboundary_apply
    (F : OrderedSimplicialMap K L) (n : ℕ) (σ : NonemptySimplex K)
    (c : Configuration (facesIn L n (F.mapFacet σ)) G)
    (τ : facesIn K (n + 1) σ) :
    F.localPullbackAddHom (n + 1) σ
        (localCoboundary L n (F.mapFacet σ) c) τ =
      localCoboundary K n σ (F.localPullbackAddHom n σ c) τ := by
  rw [localPullbackAddHom_apply, localCoboundary_apply,
    localCoboundary_apply]
  symm
  refine Fintype.sum_equiv (F.vertexEquiv τ.1.1) _ _ ?_
  intro v
  change
    incidenceSign K τ.1 v.1 •
        c (F.mapFace σ (eraseVertexIn K σ τ v.1 v.2)) =
      incidenceSign L (F.mapSimplex τ.1) (F v.1) •
        c (eraseVertexIn L (F.mapFacet σ) (F.mapFace σ τ)
          (F v.1) _)
  rw [F.incidenceSign_mapSimplex]
  rw [F.mapFace_eraseVertexIn]

/-- Pullback restricted to the range of the coboundary. -/
def pullbackCoboundary (F : OrderedSimplicialMap K L) (n : ℕ) :
    CoboundaryGroup (G := G) L n →ₗ[ℤ] CoboundaryGroup (G := G) K n :=
  LinearMap.codRestrict (coboundary K n).range
    ((F.pullback (n + 1)).comp (coboundary L n).range.subtype)
    fun b => by
      rcases b.2 with ⟨c, hc⟩
      refine ⟨F.pullback n c, ?_⟩
      change coboundary K n (F.pullback n c) = F.pullback (n + 1) b.1
      rw [← hc]
      exact (DFunLike.congr_fun (F.pullback_coboundary n) c).symm

@[simp]
theorem pullbackCoboundary_coe (F : OrderedSimplicialMap K L)
    (n : ℕ) (b : CoboundaryGroup (G := G) L n) :
    (F.pullbackCoboundary n b : Cochain K (n + 1) G) =
      F.pullback (n + 1) b.1 :=
  rfl

/-- The concrete compatible restriction morphism associated with an ordered
simplicial map.  Its direction is contravariant: from the facet data of the
target complex to that of the source complex. -/
def toFacetRestrictionHom (F : OrderedSimplicialMap K L) (n : ℕ) :
    FacetRestrictionHom
      (facetRestrictionData (G := G) L n)
      (facetRestrictionData (G := G) K n) where
  primitiveMap := (F.pullback n).toAddMonoidHom
  physicalMap := (F.pullbackCoboundary n).toAddMonoidHom
  commutes := by
    apply AddMonoidHom.ext
    intro c
    apply Subtype.ext
    exact DFunLike.congr_fun (F.pullback_coboundary n) c
  facetMap := F.mapFacet
  localPrimitiveMap := fun σ => F.localPullbackAddHom n σ
  localPhysicalMap := fun σ => F.localPullbackAddHom (n + 1) σ
  primitiveRes_commutes := by
    intro σ
    apply AddMonoidHom.ext
    intro c
    ext η
    rfl
  physicalRes_commutes := by
    intro σ
    apply AddMonoidHom.ext
    intro b
    ext τ
    rfl
  localD_commutes := by
    intro σ
    apply AddMonoidHom.ext
    intro c
    ext τ
    exact F.localPullback_coboundary_apply n σ c τ

/-- The concrete pullback on the strict primitive quotient. -/
def mapTPrime (F : OrderedSimplicialMap K L) (n : ℕ) :
    TPrime (facetRestrictionData (G := G) L n) →ₗ[ℤ]
      TPrime (facetRestrictionData (G := G) K n) :=
  FacetRestrictionHom.mapTPrime (F.toFacetRestrictionHom n)

/-- Concrete quotient pullback along the identity is the identity. -/
@[simp]
theorem mapTPrime_id (n : ℕ) :
    (id K).mapTPrime (G := G) n = LinearMap.id := by
  let LK := facetRestrictionData (G := G) K n
  calc
    (id K).mapTPrime (G := G) n =
        FacetRestrictionHom.mapTPrime (FacetRestrictionHom.id LK) := by
      apply FacetRestrictionHom.mapTPrime_eq_of_primitiveMap_eq
      change ((id K).pullback (G := G) n).toAddMonoidHom =
        AddMonoidHom.id (Cochain K n G)
      rw [pullback_id]
      rfl
    _ = LinearMap.id := FacetRestrictionHom.mapTPrime_id LK

/-- Concrete quotient pullback is strictly contravariant under composition. -/
theorem mapTPrime_comp (H : OrderedSimplicialMap L M)
    (F : OrderedSimplicialMap K L) (n : ℕ) :
    (comp H F).mapTPrime (G := G) n =
      (F.mapTPrime n).comp (H.mapTPrime n) := by
  let LM := facetRestrictionData (G := G) M n
  let LL := facetRestrictionData (G := G) L n
  let LK := facetRestrictionData (G := G) K n
  let FH := H.toFacetRestrictionHom (G := G) n
  let FF := F.toFacetRestrictionHom (G := G) n
  calc
    (comp H F).mapTPrime (G := G) n =
        FacetRestrictionHom.mapTPrime
          (FacetRestrictionHom.comp LM LL LK FF FH) := by
      apply FacetRestrictionHom.mapTPrime_eq_of_primitiveMap_eq
      change ((comp H F).pullback (G := G) n).toAddMonoidHom =
        ((F.pullback n).comp (H.pullback n)).toAddMonoidHom
      rw [pullback_comp]
    _ = (F.mapTPrime n).comp (H.mapTPrime n) :=
      FacetRestrictionHom.mapTPrime_comp LM LL LK FF FH

end FacetRestriction

end OrderedSimplicialMap

end GeneralSphereT.SimplicialCochain
