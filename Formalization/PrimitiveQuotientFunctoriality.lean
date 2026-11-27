import Formalization.PrimitiveQuotient

set_option linter.style.header false

/-!
# Functoriality of the strict primitive quotient

This module isolates the abstract content of (2.36).  A
`FacetRestrictionHom L₁ L₂` consists of compatible global maps on primitive
and physical cochains, together with compatible maps on a chosen source facet
above every target facet.  It induces linear maps on `Zprim`, `Bprim`, and
`TPrime`.  Identity and composition are proved on the nose.

For a simplicial map `f : M → N`, the intended morphism points from the data
of `N` to the data of `M` and its global maps are cochain pullbacks.  Thus the
covariance below is exactly the strict contravariance asserted in (2.36).
Choosing a maximal facet of `N` above each maximal facet of `M` is only a way to
certify local vanishing; the induced quotient map depends solely on the global
primitive pullback.  The concrete simplicial-cochain construction is left to
the module which instantiates `FacetRestrictionData`.
-/

noncomputable section

namespace GeneralSphereT.PathAlgebra

open FacetRestrictionData

universe uF₁ uF₂ uC₁ uC₂ uB₁ uB₂ uCA₁ uCA₂ uBA₁ uBA₂

section CompositionLemmas

variable {X Y Z : Type*}
variable [AddCommGroup X] [AddCommGroup Y] [AddCommGroup Z]

/-- Pushforward of free distributions respects composition. -/
theorem mapDist_comp_apply (f : X →+ Y) (g : Y →+ Z) (u : Dist X) :
    mapDist g (mapDist f u) = mapDist (g.comp f) u := by
  have h : (mapDist g).comp (mapDist f) = mapDist (g.comp f) := by
    ext x
    simp [mapDist]
  exact LinearMap.congr_fun h u

/-- Pushforward of reduced distributions respects composition. -/
theorem mapRedDist_comp_apply (f : X →+ Y) (g : Y →+ Z)
    (u : RedDist X) :
    mapRedDist g (mapRedDist f u) = mapRedDist (g.comp f) u := by
  apply Subtype.ext
  exact mapDist_comp_apply f g u.1

/-- The identity map acts trivially on reduced distributions. -/
theorem mapRedDist_id_apply (u : RedDist X) :
    mapRedDist (AddMonoidHom.id X) u = u := by
  apply Subtype.ext
  change mapDist (AddMonoidHom.id X) u.1 = u.1
  have h : mapDist (AddMonoidHom.id X) = LinearMap.id := by
    ext x
    simp [mapDist]
  exact LinearMap.congr_fun h u.1

variable {I J K : Type*}
variable [AddCommGroup I] [AddCommGroup J] [AddCommGroup K]

/-- Mapping both labels of a path respects composition. -/
theorem mapPath_comp_apply
    (i₁ : I →+ J) (b₁ : X →+ Y)
    (i₂ : J →+ K) (b₂ : Y →+ Z) (p : Path I X) :
    mapPath i₂ b₂ (mapPath i₁ b₁ p) =
      mapPath (i₂.comp i₁) (b₂.comp b₁) p := by
  refine Submodule.Quotient.induction_on
    (p := zeroIncrement I X) p ?_
  intro q
  have hraw :
      (rawMapPath i₂ b₂).comp (rawMapPath i₁ b₁) =
        rawMapPath (i₂.comp i₁) (b₂.comp b₁) := by
    ext a
    simp [rawMapPath]
  change
    (zeroIncrement K Z).mkQ
        (rawMapPath i₂ b₂ (rawMapPath i₁ b₁ q)) =
      (zeroIncrement K Z).mkQ
        (rawMapPath (i₂.comp i₁) (b₂.comp b₁) q)
  exact congrArg (zeroIncrement K Z).mkQ (LinearMap.congr_fun hraw q)

/-- Mapping a path by identity maps does nothing. -/
theorem mapPath_id_apply (p : Path I X) :
    mapPath (AddMonoidHom.id I) (AddMonoidHom.id X) p = p := by
  refine Submodule.Quotient.induction_on
    (p := zeroIncrement I X) p ?_
  intro q
  have hraw :
      rawMapPath (AddMonoidHom.id I) (AddMonoidHom.id X) = LinearMap.id := by
    ext a
    simp [rawMapPath]
  change
    (zeroIncrement I X).mkQ
        (rawMapPath (AddMonoidHom.id I) (AddMonoidHom.id X) q) =
      (zeroIncrement I X).mkQ q
  exact congrArg (zeroIncrement I X).mkQ (LinearMap.congr_fun hraw q)

end CompositionLemmas

section Morphism

variable {C₁ : Type uC₁} {B₁ : Type uB₁}
variable {C₂ : Type uC₂} {B₂ : Type uB₂}
variable [AddCommGroup C₁] [AddCommGroup B₁]
variable [AddCommGroup C₂] [AddCommGroup B₂]
variable {Facet₁ : Type uF₁} {Facet₂ : Type uF₂}
variable {CAt₁ : Facet₁ → Type uCA₁} {BAt₁ : Facet₁ → Type uBA₁}
variable {CAt₂ : Facet₂ → Type uCA₂} {BAt₂ : Facet₂ → Type uBA₂}
variable [∀ ρ, AddCommGroup (CAt₁ ρ)] [∀ ρ, AddCommGroup (BAt₁ ρ)]
variable [∀ ρ, AddCommGroup (CAt₂ ρ)] [∀ ρ, AddCommGroup (BAt₂ ρ)]
variable {d₁ : C₁ →+ B₁} {d₂ : C₂ →+ B₂}

variable (L₁ : FacetRestrictionData
  (CAt := CAt₁) (BAt := BAt₁) (Facet := Facet₁) d₁)
variable (L₂ : FacetRestrictionData
  (CAt := CAt₂) (BAt := BAt₂) (Facet := Facet₂) d₂)

/--
A compatible map between two systems of facet restrictions.

The direction is the direction of the induced maps on cochains.  Consequently,
a simplicial map `M → N` gives a morphism from the restriction data of `N`
to that of `M`.
-/
structure FacetRestrictionHom where
  primitiveMap : C₁ →+ C₂
  physicalMap : B₁ →+ B₂
  commutes : physicalMap.comp d₁ = d₂.comp primitiveMap
  facetMap : Facet₂ → Facet₁
  localPrimitiveMap : ∀ ρ : Facet₂, CAt₁ (facetMap ρ) →+ CAt₂ ρ
  localPhysicalMap : ∀ ρ : Facet₂, BAt₁ (facetMap ρ) →+ BAt₂ ρ
  primitiveRes_commutes : ∀ ρ : Facet₂,
    (L₂.primitiveRes ρ).comp primitiveMap =
      (localPrimitiveMap ρ).comp (L₁.primitiveRes (facetMap ρ))
  physicalRes_commutes : ∀ ρ : Facet₂,
    (L₂.physicalRes ρ).comp physicalMap =
      (localPhysicalMap ρ).comp (L₁.physicalRes (facetMap ρ))
  localD_commutes : ∀ ρ : Facet₂,
    (localPhysicalMap ρ).comp (L₁.localD (facetMap ρ)) =
      (L₂.localD ρ).comp (localPrimitiveMap ρ)

namespace FacetRestrictionHom

variable {L₁ L₂}

/-- A compatible facet map carries locally-zero reduced distributions to
locally-zero reduced distributions. -/
theorem mapRedDist_mem_locallyZero
    (F : FacetRestrictionHom L₁ L₂) {z : RedDist C₁}
    (hz : z ∈ L₁.locallyZeroRedDist) :
    mapRedDist F.primitiveMap z ∈ L₂.locallyZeroRedDist := by
  rw [locallyZeroRedDist, Submodule.mem_iInf]
  intro ρ
  rw [LinearMap.mem_ker]
  have hzρ : L₁.restrictRedDist (F.facetMap ρ) z = 0 :=
    LinearMap.mem_ker.mp
      ((Submodule.mem_iInf (fun σ : Facet₁ =>
        LinearMap.ker (L₁.restrictRedDist σ))).1 hz (F.facetMap ρ))
  apply Subtype.ext
  change mapDist (L₂.primitiveRes ρ)
      (mapDist F.primitiveMap z.1) = 0
  rw [mapDist_comp_apply]
  rw [F.primitiveRes_commutes ρ]
  rw [← mapDist_comp_apply]
  change mapDist (F.localPrimitiveMap ρ)
      ((L₁.restrictRedDist (F.facetMap ρ) z :
        RedDist (CAt₁ (F.facetMap ρ))) : Dist _) = 0
  rw [hzρ]
  simp

/-- A compatible facet map carries locally-zero primitive paths to
locally-zero primitive paths. -/
theorem mapPath_mem_locallyZero
    (F : FacetRestrictionHom L₁ L₂) {R : Path C₁ C₁}
    (hR : R ∈ L₁.locallyZeroPrimitivePath) :
    mapPath F.primitiveMap F.primitiveMap R ∈
      L₂.locallyZeroPrimitivePath := by
  rw [locallyZeroPrimitivePath, Submodule.mem_iInf]
  intro ρ
  rw [LinearMap.mem_ker]
  have hRρ : L₁.restrictPrimitivePath (F.facetMap ρ) R = 0 :=
    LinearMap.mem_ker.mp
      ((Submodule.mem_iInf (fun σ : Facet₁ =>
        LinearMap.ker (L₁.restrictPrimitivePath σ))).1 hR (F.facetMap ρ))
  change mapPath (L₂.primitiveRes ρ) (L₂.primitiveRes ρ)
      (mapPath F.primitiveMap F.primitiveMap R) = 0
  rw [mapPath_comp_apply]
  rw [F.primitiveRes_commutes ρ]
  rw [← mapPath_comp_apply]
  change mapPath (F.localPrimitiveMap ρ) (F.localPrimitiveMap ρ)
      (L₁.restrictPrimitivePath (F.facetMap ρ) R) = 0
  rw [hRρ]
  simp

/-- Naturality of `d_*` on primitive paths under a compatible morphism. -/
theorem mapDPath_mapPath
    (F : FacetRestrictionHom L₁ L₂) (R : Path C₁ C₁) :
    mapDPath d₂ (mapPath F.primitiveMap F.primitiveMap R) =
      mapPath F.primitiveMap F.physicalMap (mapDPath d₁ R) := by
  change
    mapPath (AddMonoidHom.id C₂) d₂
        (mapPath F.primitiveMap F.primitiveMap R) =
      mapPath F.primitiveMap F.physicalMap
        (mapPath (AddMonoidHom.id C₁) d₁ R)
  rw [mapPath_comp_apply, mapPath_comp_apply]
  have hbase : d₂.comp F.primitiveMap = F.physicalMap.comp d₁ :=
    F.commutes.symm
  rw [hbase]
  rfl

/-- Compatible maps preserve relation paths defining `Bprim`. -/
theorem mapPath_mem_relationPaths
    (F : FacetRestrictionHom L₁ L₂) {R : Path C₁ C₁}
    (hR : R ∈ relationPaths L₁) :
    mapPath F.primitiveMap F.primitiveMap R ∈ relationPaths L₂ := by
  rw [relationPaths_eq] at hR ⊢
  refine ⟨?_, mapPath_mem_locallyZero F hR.2⟩
  change mapDPath d₂ (mapPath F.primitiveMap F.primitiveMap R) = 0
  rw [mapDPath_mapPath F R]
  rw [LinearMap.mem_ker.mp hR.1]
  simp

/-- Compatible maps preserve primitive cycles. -/
theorem mapRedDist_mem_Zprim
    (F : FacetRestrictionHom L₁ L₂) {z : RedDist C₁}
    (hz : z ∈ Zprim L₁) :
    mapRedDist F.primitiveMap z ∈ Zprim L₂ := by
  refine ⟨?_, mapRedDist_mem_locallyZero F hz.2⟩
  change mapRedDist d₂ (mapRedDist F.primitiveMap z) = 0
  calc
    mapRedDist d₂ (mapRedDist F.primitiveMap z) =
        mapRedDist (d₂.comp F.primitiveMap) z :=
      mapRedDist_comp_apply F.primitiveMap d₂ z
    _ = mapRedDist (F.physicalMap.comp d₁) z := by
      rw [F.commutes]
    _ = mapRedDist F.physicalMap (mapRedDist d₁ z) := by
      symm
      exact mapRedDist_comp_apply d₁ F.physicalMap z
    _ = 0 := by rw [LinearMap.mem_ker.mp hz.1]; simp

/-- The induced linear map on primitive cycles. -/
def mapZprim (F : FacetRestrictionHom L₁ L₂) :
    Zprim L₁ →ₗ[ℤ] Zprim L₂ :=
  LinearMap.codRestrict (Zprim L₂)
    ((mapRedDist F.primitiveMap).comp (Zprim L₁).subtype)
    fun z => mapRedDist_mem_Zprim F z.property

@[simp]
theorem mapZprim_coe (F : FacetRestrictionHom L₁ L₂)
    (z : Zprim L₁) :
    (((mapZprim F z : Zprim L₂) : RedDist C₂) : Dist C₂) =
      mapDist F.primitiveMap (z : RedDist C₁).1 :=
  rfl

/-- Compatible maps carry `Bprim` into `Bprim`. -/
theorem mapRedDist_mem_Bprim
    (F : FacetRestrictionHom L₁ L₂) {z : RedDist C₁}
    (hz : z ∈ Bprim L₁) :
    mapRedDist F.primitiveMap z ∈ Bprim L₂ := by
  rcases hz with ⟨R, hR, rfl⟩
  rw [Bprim]
  refine ⟨mapPath F.primitiveMap F.primitiveMap R,
    mapPath_mem_relationPaths F hR, ?_⟩
  exact (LinearMap.congr_fun
    (reducedBoundary_natural (AddMonoidHom.id C₁)
      (AddMonoidHom.id C₂) F.primitiveMap F.primitiveMap rfl) R).symm

/-- The denominator of `TPrime` is preserved by the cycle map. -/
theorem BprimInZprim_le_comap_mapZprim
    (F : FacetRestrictionHom L₁ L₂) :
    BprimInZprim L₁ ≤ (BprimInZprim L₂).comap (mapZprim F) := by
  intro z hz
  change ((mapZprim F z : Zprim L₂) : RedDist C₂) ∈ Bprim L₂
  apply mapRedDist_mem_Bprim F
  exact hz

/-- The map on strict primitive quotients induced by compatible pullback data. -/
def mapTPrime (F : FacetRestrictionHom L₁ L₂) :
    TPrime L₁ →ₗ[ℤ] TPrime L₂ :=
  (BprimInZprim L₁).mapQ (BprimInZprim L₂) (mapZprim F)
    (BprimInZprim_le_comap_mapZprim F)

@[simp]
theorem mapTPrime_mkQ (F : FacetRestrictionHom L₁ L₂)
    (z : Zprim L₁) :
    mapTPrime F ((BprimInZprim L₁).mkQ z) =
      (BprimInZprim L₂).mkQ (mapZprim F z) := by
  exact Submodule.mapQ_apply (BprimInZprim L₁)
    (BprimInZprim L₂) (mapZprim F) z

/-- The cycle map depends only on the global primitive map, not on the facet
witnesses used to certify locality. -/
theorem mapZprim_eq_of_primitiveMap_eq
    (F G : FacetRestrictionHom L₁ L₂)
    (h : F.primitiveMap = G.primitiveMap) :
    mapZprim F = mapZprim G := by
  apply LinearMap.ext
  intro z
  apply Subtype.ext
  change mapRedDist F.primitiveMap z.1 = mapRedDist G.primitiveMap z.1
  rw [h]

/-- Consequently the induced map on `TPrime` is independent of all chosen
facet witnesses and local comparison maps. -/
theorem mapTPrime_eq_of_primitiveMap_eq
    (F G : FacetRestrictionHom L₁ L₂)
    (h : F.primitiveMap = G.primitiveMap) :
    mapTPrime F = mapTPrime G := by
  apply LinearMap.ext
  intro x
  refine Submodule.Quotient.induction_on
    (p := BprimInZprim L₁) x ?_
  intro z
  change mapTPrime F ((BprimInZprim L₁).mkQ z) =
    mapTPrime G ((BprimInZprim L₁).mkQ z)
  rw [mapTPrime_mkQ, mapTPrime_mkQ]
  rw [LinearMap.congr_fun (mapZprim_eq_of_primitiveMap_eq F G h) z]

end FacetRestrictionHom

end Morphism

section IdentityAndComposition

variable {C₁ : Type uC₁} {B₁ : Type uB₁}
variable {C₂ : Type uC₂} {B₂ : Type uB₂}
variable {C₃ B₃ : Type*}
variable [AddCommGroup C₁] [AddCommGroup B₁]
variable [AddCommGroup C₂] [AddCommGroup B₂]
variable [AddCommGroup C₃] [AddCommGroup B₃]
variable {Facet₁ : Type uF₁} {Facet₂ : Type uF₂} {Facet₃ : Type*}
variable {CAt₁ : Facet₁ → Type uCA₁} {BAt₁ : Facet₁ → Type uBA₁}
variable {CAt₂ : Facet₂ → Type uCA₂} {BAt₂ : Facet₂ → Type uBA₂}
variable {CAt₃ : Facet₃ → Type*} {BAt₃ : Facet₃ → Type*}
variable [∀ ρ, AddCommGroup (CAt₁ ρ)] [∀ ρ, AddCommGroup (BAt₁ ρ)]
variable [∀ ρ, AddCommGroup (CAt₂ ρ)] [∀ ρ, AddCommGroup (BAt₂ ρ)]
variable [∀ ρ, AddCommGroup (CAt₃ ρ)] [∀ ρ, AddCommGroup (BAt₃ ρ)]
variable {d₁ : C₁ →+ B₁} {d₂ : C₂ →+ B₂} {d₃ : C₃ →+ B₃}

variable (L₁ : FacetRestrictionData
  (CAt := CAt₁) (BAt := BAt₁) (Facet := Facet₁) d₁)
variable (L₂ : FacetRestrictionData
  (CAt := CAt₂) (BAt := BAt₂) (Facet := Facet₂) d₂)
variable (L₃ : FacetRestrictionData
  (CAt := CAt₃) (BAt := BAt₃) (Facet := Facet₃) d₃)

namespace FacetRestrictionHom

/-- Identity compatible morphism. -/
def id (L₁ : FacetRestrictionData
    (CAt := CAt₁) (BAt := BAt₁) (Facet := Facet₁) d₁) :
    FacetRestrictionHom L₁ L₁ where
  primitiveMap := AddMonoidHom.id C₁
  physicalMap := AddMonoidHom.id B₁
  commutes := rfl
  facetMap := _root_.id
  localPrimitiveMap := fun ρ => AddMonoidHom.id (CAt₁ ρ)
  localPhysicalMap := fun ρ => AddMonoidHom.id (BAt₁ ρ)
  primitiveRes_commutes := fun _ => rfl
  physicalRes_commutes := fun _ => rfl
  localD_commutes := fun _ => rfl

/-- Composition of compatible morphisms. -/
def comp (G : FacetRestrictionHom L₂ L₃)
    (F : FacetRestrictionHom L₁ L₂) :
    FacetRestrictionHom L₁ L₃ where
  primitiveMap := G.primitiveMap.comp F.primitiveMap
  physicalMap := G.physicalMap.comp F.physicalMap
  commutes := by
    ext x
    have hF : F.physicalMap (d₁ x) = d₂ (F.primitiveMap x) := by
      simpa using DFunLike.congr_fun F.commutes x
    have hG : G.physicalMap (d₂ (F.primitiveMap x)) =
        d₃ (G.primitiveMap (F.primitiveMap x)) := by
      simpa using DFunLike.congr_fun G.commutes (F.primitiveMap x)
    exact (congrArg G.physicalMap hF).trans hG
  facetMap := fun ρ => F.facetMap (G.facetMap ρ)
  localPrimitiveMap := fun ρ =>
    (G.localPrimitiveMap ρ).comp (F.localPrimitiveMap (G.facetMap ρ))
  localPhysicalMap := fun ρ =>
    (G.localPhysicalMap ρ).comp (F.localPhysicalMap (G.facetMap ρ))
  primitiveRes_commutes := by
    intro ρ
    ext x
    change L₃.primitiveRes ρ (G.primitiveMap (F.primitiveMap x)) =
      G.localPrimitiveMap ρ
        (F.localPrimitiveMap (G.facetMap ρ)
          (L₁.primitiveRes (F.facetMap (G.facetMap ρ)) x))
    have hG : L₃.primitiveRes ρ (G.primitiveMap (F.primitiveMap x)) =
        G.localPrimitiveMap ρ
          (L₂.primitiveRes (G.facetMap ρ) (F.primitiveMap x)) := by
      simpa using DFunLike.congr_fun
        (G.primitiveRes_commutes ρ) (F.primitiveMap x)
    have hF : L₂.primitiveRes (G.facetMap ρ) (F.primitiveMap x) =
        F.localPrimitiveMap (G.facetMap ρ)
          (L₁.primitiveRes (F.facetMap (G.facetMap ρ)) x) := by
      simpa using DFunLike.congr_fun
        (F.primitiveRes_commutes (G.facetMap ρ)) x
    exact hG.trans (congrArg (G.localPrimitiveMap ρ) hF)
  physicalRes_commutes := by
    intro ρ
    ext x
    change L₃.physicalRes ρ (G.physicalMap (F.physicalMap x)) =
      G.localPhysicalMap ρ
        (F.localPhysicalMap (G.facetMap ρ)
          (L₁.physicalRes (F.facetMap (G.facetMap ρ)) x))
    have hG : L₃.physicalRes ρ (G.physicalMap (F.physicalMap x)) =
        G.localPhysicalMap ρ
          (L₂.physicalRes (G.facetMap ρ) (F.physicalMap x)) := by
      simpa using DFunLike.congr_fun
        (G.physicalRes_commutes ρ) (F.physicalMap x)
    have hF : L₂.physicalRes (G.facetMap ρ) (F.physicalMap x) =
        F.localPhysicalMap (G.facetMap ρ)
          (L₁.physicalRes (F.facetMap (G.facetMap ρ)) x) := by
      simpa using DFunLike.congr_fun
        (F.physicalRes_commutes (G.facetMap ρ)) x
    exact hG.trans (congrArg (G.localPhysicalMap ρ) hF)
  localD_commutes := by
    intro ρ
    ext x
    change G.localPhysicalMap ρ
        (F.localPhysicalMap (G.facetMap ρ)
          (L₁.localD (F.facetMap (G.facetMap ρ)) x)) =
      L₃.localD ρ
        (G.localPrimitiveMap ρ
          (F.localPrimitiveMap (G.facetMap ρ) x))
    have hF : F.localPhysicalMap (G.facetMap ρ)
          (L₁.localD (F.facetMap (G.facetMap ρ)) x) =
        L₂.localD (G.facetMap ρ)
          (F.localPrimitiveMap (G.facetMap ρ) x) := by
      simpa using DFunLike.congr_fun
        (F.localD_commutes (G.facetMap ρ)) x
    have hG : G.localPhysicalMap ρ
          (L₂.localD (G.facetMap ρ)
            (F.localPrimitiveMap (G.facetMap ρ) x)) =
        L₃.localD ρ
          (G.localPrimitiveMap ρ
            (F.localPrimitiveMap (G.facetMap ρ) x)) := by
      simpa using DFunLike.congr_fun (G.localD_commutes ρ)
        (F.localPrimitiveMap (G.facetMap ρ) x)
    exact (congrArg (G.localPhysicalMap ρ) hF).trans hG

@[simp]
theorem mapZprim_id :
    mapZprim (id L₁) = LinearMap.id := by
  apply LinearMap.ext
  intro z
  apply Subtype.ext
  exact mapRedDist_id_apply z.1

theorem mapZprim_comp
    (G : FacetRestrictionHom L₂ L₃)
    (F : FacetRestrictionHom L₁ L₂) :
    mapZprim (FacetRestrictionHom.comp L₁ L₂ L₃ G F) =
      (mapZprim G).comp (mapZprim F) := by
  apply LinearMap.ext
  intro z
  apply Subtype.ext
  exact (mapRedDist_comp_apply F.primitiveMap G.primitiveMap z.1).symm

@[simp]
theorem mapTPrime_id :
    mapTPrime (id L₁) = LinearMap.id := by
  apply LinearMap.ext
  intro x
  refine Submodule.Quotient.induction_on
    (p := BprimInZprim L₁) x ?_
  intro z
  change mapTPrime (id L₁) ((BprimInZprim L₁).mkQ z) =
    (BprimInZprim L₁).mkQ z
  rw [mapTPrime_mkQ]
  rw [LinearMap.congr_fun (mapZprim_id L₁) z]
  rfl

theorem mapTPrime_comp
    (G : FacetRestrictionHom L₂ L₃)
    (F : FacetRestrictionHom L₁ L₂) :
    mapTPrime (FacetRestrictionHom.comp L₁ L₂ L₃ G F) =
      (mapTPrime G).comp (mapTPrime F) := by
  apply LinearMap.ext
  intro x
  refine Submodule.Quotient.induction_on
    (p := BprimInZprim L₁) x ?_
  intro z
  change
    mapTPrime (FacetRestrictionHom.comp L₁ L₂ L₃ G F)
        ((BprimInZprim L₁).mkQ z) =
      mapTPrime G (mapTPrime F ((BprimInZprim L₁).mkQ z))
  simp only [mapTPrime_mkQ]
  rw [LinearMap.congr_fun (mapZprim_comp L₁ L₂ L₃ G F) z]
  rfl

end FacetRestrictionHom

end IdentityAndComposition

end GeneralSphereT.PathAlgebra
