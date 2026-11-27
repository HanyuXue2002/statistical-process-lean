import Formalization.Section4NormalizedChainDoldKanMap

set_option linter.style.header false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits Opposite Simplicial
open AlgebraicTopology.DoldKan

namespace GeneralSphereT.SimplicialCochain

universe u

variable {V W G : Type u}
variable [LinearOrder V] [LinearOrder W]
variable [Fintype V] [Fintype W]
variable [AddCommGroup G]
variable {K : AbstractSimplicialComplex V}
variable {M : AbstractSimplicialComplex W}

/-- An ordered simplicial embedding preserves nondegenerate simplices. -/
def OrderedSimplicialMap.mapNonDegenerate
  (F : OrderedSimplicialMap K M) (n : ℕ) :
    (orderedComplexSSet K).nonDegenerate n →
      (orderedComplexSSet M).nonDegenerate n :=
  fun x => ⟨F.toSSetMap.app _ x.1, by
    rw [mem_orderedComplexSSet_nonDegenerate_iff_injective]
    change Function.Injective (F.toOrderEmbedding.toOrderHom.comp x.1.1)
    exact F.toOrderEmbedding.injective.comp
      ((mem_orderedComplexSSet_nonDegenerate_iff_injective K x.1).1 x.2)⟩

@[simp]
theorem OrderedSimplicialMap.mapNonDegenerate_val
    (F : OrderedSimplicialMap K M) (n : ℕ)
    (x : (orderedComplexSSet K).nonDegenerate n) :
    (F.mapNonDegenerate n x).1 = F.toSSetMap.app _ x.1 :=
  rfl

/-- The canonical split free simplicial abelian group attached to an
ordered complex. -/
abbrev orderedFreeSplit (K : AbstractSimplicialComplex V) :
    SimplicialObject.Split AddCommGrpCat.{u} :=
  SimplicialObject.Split.mk'
    ((orderedComplexSSet K).splitting.map
      (sigmaConst.obj integralCoefficients))

/-- The degreewise free map induced by a map of ordered complexes. -/
abbrev freeSimplicialAbelianMap (F : OrderedSimplicialMap K M) :
    freeSimplicialAbelian (orderedComplexSSet K) ⟶
      freeSimplicialAbelian (orderedComplexSSet M) :=
  ((SimplicialObject.whiskering _ _).obj
    (sigmaConst.obj integralCoefficients)).map F.toSSetMap

/-- The free additive map on nondegenerate simplices in one degree. -/
def orderedNondegenerateFreeMap
    (F : OrderedSimplicialMap K M) (n : ℕ) :=
  (sigmaConst.obj integralCoefficients).map
    (↾ fun x => F.mapNonDegenerate n x)

/-- The same degree map, with source and target displayed as the degrees of
Mathlib's normalized chain complexes. -/
def orderedNormalizedChainMap
    (F : OrderedSimplicialMap K M) (n : ℕ) :
    ((orderedComplexSSet K).normalizedChainComplex
        (integralCoefficients : AddCommGrpCat.{u})).X n ⟶
      ((orderedComplexSSet M).normalizedChainComplex
        (integralCoefficients : AddCommGrpCat.{u})).X n := by
  change (sigmaConst.obj integralCoefficients).obj
      ((orderedComplexSSet K).nonDegenerate n) ⟶
    (sigmaConst.obj integralCoefficients).obj
      ((orderedComplexSSet M).nonDegenerate n)
  exact orderedNondegenerateFreeMap F n

/-- An ordered simplicial embedding induces a morphism of the canonical
splittings, since it sends every nondegenerate simplex to a nondegenerate
simplex. -/
def orderedFreeSplitMap (F : OrderedSimplicialMap K M) :
    orderedFreeSplit K ⟶ orderedFreeSplit M where
  F := freeSimplicialAbelianMap F
  f n := orderedNondegenerateFreeMap F n
  comm n := by
    change (sigmaConst.obj integralCoefficients).map
          (↾ fun x : (orderedComplexSSet K).nonDegenerate n => x.1) ≫
        (sigmaConst.obj integralCoefficients).map
          (F.toSSetMap.app (Opposite.op (SimplexCategory.mk n))) =
      (sigmaConst.obj integralCoefficients).map
          (↾ fun x => F.mapNonDegenerate n x) ≫
        (sigmaConst.obj integralCoefficients).map
          (↾ fun x : (orderedComplexSSet M).nonDegenerate n => x.1)
    rw [← Functor.map_comp, ← Functor.map_comp]
    congr 1

/-- The map on nondegenerate chains commutes with the canonical inclusion
back into the unnormalized chain complex. -/
theorem orderedFreeSplitMap_comp_fromNormalized
    (F : OrderedSimplicialMap K M) (n : ℕ) :
    orderedNormalizedChainMap F n ≫
      ((orderedComplexSSet M).fromNormalizedChainComplex
        integralCoefficients).f n =
    ((orderedComplexSSet K).fromNormalizedChainComplex
        integralCoefficients).f n ≫
      (SSet.chainComplexMap (C := AddCommGrpCat.{u}) F.toSSetMap
        integralCoefficients).f n := by
  dsimp [orderedNormalizedChainMap, SSet.fromNormalizedChainComplex]
  rw [SimplicialObject.Splitting.fromNondegComplex_f,
    SimplicialObject.Splitting.fromNondegComplex_f]
  have hcomm :
      ((orderedComplexSSet K).splitting.map
          (sigmaConst.obj integralCoefficients)).ι n ≫
        (freeSimplicialAbelianMap F).app _ =
      orderedNondegenerateFreeMap F n ≫
        ((orderedComplexSSet M).splitting.map
          (sigmaConst.obj integralCoefficients)).ι n :=
    (orderedFreeSplitMap F).comm n
  have hcommP := congrArg (fun k => k ≫
    (AlgebraicTopology.DoldKan.PInfty
      (X := freeSimplicialAbelian (orderedComplexSSet M))).f n) hcomm.symm
  calc
    _ = (((orderedComplexSSet K).splitting.map
          (sigmaConst.obj integralCoefficients)).ι n ≫
        (freeSimplicialAbelianMap F).app _) ≫
        (AlgebraicTopology.DoldKan.PInfty
          (X := freeSimplicialAbelian (orderedComplexSSet M))).f n := hcommP
    _ = ((orderedComplexSSet K).splitting.map
          (sigmaConst.obj integralCoefficients)).ι n ≫
        (AlgebraicTopology.DoldKan.PInfty
          (X := freeSimplicialAbelian (orderedComplexSSet K))).f n ≫
        (freeSimplicialAbelianMap F).app _ := by
      simp only [Category.assoc]
      rw [AlgebraicTopology.DoldKan.PInfty_f_naturality]
    _ = ((orderedComplexSSet K).splitting.map
          (sigmaConst.obj integralCoefficients)).ι n ≫
        (AlgebraicTopology.DoldKan.PInfty
          (X := freeSimplicialAbelian (orderedComplexSSet K))).f n ≫
        (SSet.chainComplexMap (C := AddCommGrpCat.{u}) F.toSSetMap
          integralCoefficients).f n := rfl

/-- The map on nondegenerate chains sends the normalized generator of a
simplex to the normalized generator of its image. -/
theorem orderedFreeSplitMap_ιNormalizedChainComplex
    (F : OrderedSimplicialMap K M) (n : ℕ)
    (x : (orderedComplexSSet K).obj
      (Opposite.op (SimplexCategory.mk n))) :
    (orderedComplexSSet K).ιNormalizedChainComplex
        (R := (integralCoefficients : AddCommGrpCat.{u})) x ≫
      orderedNormalizedChainMap F n =
    (orderedComplexSSet M).ιNormalizedChainComplex
      (R := (integralCoefficients : AddCommGrpCat.{u}))
        (F.toSSetMap.app _ x) := by
  let j := ((orderedComplexSSet M).fromNormalizedChainComplex
    (integralCoefficients : AddCommGrpCat.{u})).f n
  let p := ((orderedComplexSSet M).toNormalizedChainComplex
    (integralCoefficients : AddCommGrpCat.{u})).f n
  have hcomp :
      ((orderedComplexSSet K).ιNormalizedChainComplex
          (R := (integralCoefficients : AddCommGrpCat.{u})) x ≫
        orderedNormalizedChainMap F n) ≫ j =
      (orderedComplexSSet M).ιNormalizedChainComplex
          (R := (integralCoefficients : AddCommGrpCat.{u}))
            (F.toSSetMap.app _ x) ≫ j := by
    dsimp [j]
    rw [Category.assoc, orderedFreeSplitMap_comp_fromNormalized]
    rw [← Category.assoc,
      SSet.ιNormalizedChainComplex_fromNormalizedChainComplex_f,
      SSet.ιNormalizedChainComplex_fromNormalizedChainComplex_f]
    change (orderedComplexSSet K).ιChainComplex x ≫
        (AlgebraicTopology.DoldKan.PInfty
          (X := freeSimplicialAbelian (orderedComplexSSet K))).f n ≫
        (freeSimplicialAbelianMap F).app _ =
      (orderedComplexSSet M).ιChainComplex (F.toSSetMap.app _ x) ≫
        (AlgebraicTopology.DoldKan.PInfty
          (X := freeSimplicialAbelian (orderedComplexSSet M))).f n
    rw [← AlgebraicTopology.DoldKan.PInfty_f_naturality]
    rw [← Category.assoc]
    change ((orderedComplexSSet K).ιChainComplex x ≫
        (SSet.chainComplexMap (C := AddCommGrpCat.{u})
          F.toSSetMap integralCoefficients).f n) ≫
      (AlgebraicTopology.DoldKan.PInfty
        (X := freeSimplicialAbelian (orderedComplexSSet M))).f n = _
    rw [SSet.ι_chainComplexMap_f]
  calc
    _ = (((orderedComplexSSet K).ιNormalizedChainComplex
          (R := (integralCoefficients : AddCommGrpCat.{u})) x ≫
        orderedNormalizedChainMap F n) ≫ j) ≫ p := by
      dsimp [j, p]
      rw [Category.assoc,
        SSet.fromNormalizedChainComplex_f_toNormalizedChainComplex_f]
      simp
    _ = ((orderedComplexSSet M).ιNormalizedChainComplex
          (R := (integralCoefficients : AddCommGrpCat.{u}))
            (F.toSSetMap.app _ x) ≫ j) ≫ p :=
      congrArg (fun k => k ≫ p) hcomp
    _ = _ := by
      dsimp [j, p]
      rw [Category.assoc,
        SSet.fromNormalizedChainComplex_f_toNormalizedChainComplex_f]
      simp

/-- Componentwise form of functoriality of normalized chains for an ordered
simplicial embedding. -/
theorem normalizedChainComplexMap_f_eq_orderedFreeSplitMap_f
    (F : OrderedSimplicialMap K M) (n : ℕ) :
    (SSet.normalizedChainComplexMap (C := AddCommGrpCat.{u}) F.toSSetMap
      (integralCoefficients : AddCommGrpCat.{u})).f n =
        orderedNormalizedChainMap F n := by
  apply (orderedComplexSSet K).normalizedChainComplex_hom_ext
    (R := (integralCoefficients : AddCommGrpCat.{u}))
  intro x hx
  rw [SSet.ι_normalizedChainComplexMap_f]
  symm
  exact orderedFreeSplitMap_ιNormalizedChainComplex F n x

/-- The nondegenerate-complex map carried by the split morphism is exactly
Mathlib's functorial normalized-chain map. -/
theorem orderedFreeSplitMap_nondegComplex
    (F : OrderedSimplicialMap K M) :
    SSet.normalizedChainComplexMap (C := AddCommGrpCat.{u}) F.toSSetMap
        (integralCoefficients : AddCommGrpCat.{u}) =
      (SimplicialObject.Split.nondegComplexFunctor.map
        (orderedFreeSplitMap F)) := by
  apply HomologicalComplex.hom_ext
  intro n
  exact normalizedChainComplexMap_f_eq_orderedFreeSplitMap_f F n

/-- The Karoubi-envelope isomorphism whose fully faithful preimage is
`normalizedChainIsoDoldKanN`. -/
abbrev orderedKaroubiNormalizedIso (K : AbstractSimplicialComplex V) :=
  ((orderedComplexSSet K).splitting.map
      (sigmaConst.obj (integralCoefficients : AddCommGrpCat.{u}))).toKaroubiNondegComplexIsoN₁ ≪≫
    (N₁_iso_normalizedMooreComplex_comp_toKaroubi
      AddCommGrpCat.{u}).app
        (freeSimplicialAbelian (orderedComplexSSet K))

/-- Naturality of the preceding comparison inside the Karoubi envelope. -/
theorem orderedKaroubiNormalizedIso_naturality
    (F : OrderedSimplicialMap K M) :
    (CategoryTheory.Idempotents.toKaroubi
        (ChainComplex AddCommGrpCat.{u} ℕ)).map
          (SSet.normalizedChainComplexMap
            (C := AddCommGrpCat.{u}) F.toSSetMap
            (integralCoefficients : AddCommGrpCat.{u})) ≫
        (orderedKaroubiNormalizedIso M).hom =
      (orderedKaroubiNormalizedIso K).hom ≫
        (CategoryTheory.Idempotents.toKaroubi
          (ChainComplex AddCommGrpCat.{u} ℕ)).map
            (CategoryTheory.Abelian.DoldKan.N.map
              (freeSimplicialAbelianMap F)) := by
  rw [orderedFreeSplitMap_nondegComplex F]
  change
    ((SimplicialObject.Split.nondegComplexFunctor ⋙
        CategoryTheory.Idempotents.toKaroubi
          (ChainComplex AddCommGrpCat.{u} ℕ)).map
          (orderedFreeSplitMap F)) ≫
        ((SimplicialObject.Split.toKaroubiNondegComplexFunctorIsoN₁
          (C := AddCommGrpCat.{u})).hom.app (orderedFreeSplit M) ≫
          (N₁_iso_normalizedMooreComplex_comp_toKaroubi
            AddCommGrpCat.{u}).hom.app
              (orderedFreeSplit M).X) =
      ((SimplicialObject.Split.toKaroubiNondegComplexFunctorIsoN₁
          (C := AddCommGrpCat.{u})).hom.app (orderedFreeSplit K) ≫
        (N₁_iso_normalizedMooreComplex_comp_toKaroubi
          AddCommGrpCat.{u}).hom.app (orderedFreeSplit K).X) ≫
        ((AlgebraicTopology.normalizedMooreComplex AddCommGrpCat.{u} ⋙
          CategoryTheory.Idempotents.toKaroubi
            (ChainComplex AddCommGrpCat.{u} ℕ)).map
              (orderedFreeSplitMap F).F)
  rw [← Category.assoc,
    (SimplicialObject.Split.toKaroubiNondegComplexFunctorIsoN₁
      (C := AddCommGrpCat.{u})).hom.naturality]
  simp only [Category.assoc]
  rw [← (N₁_iso_normalizedMooreComplex_comp_toKaroubi
    AddCommGrpCat.{u}).hom.naturality]
  rfl

/-- The normalized-chain/Dold--Kan comparison used in the construction is
natural for ordered simplicial embeddings. -/
theorem normalizedChainIsoDoldKanN_naturality
    (F : OrderedSimplicialMap K M) :
    SSet.normalizedChainComplexMap
          (C := AddCommGrpCat.{u}) F.toSSetMap
          (integralCoefficients : AddCommGrpCat.{u}) ≫
        (normalizedChainIsoDoldKanN (orderedComplexSSet M)).hom =
      (normalizedChainIsoDoldKanN (orderedComplexSSet K)).hom ≫
        CategoryTheory.Abelian.DoldKan.N.map
          (freeSimplicialAbelianMap F) := by
  apply (CategoryTheory.Idempotents.toKaroubi
    (ChainComplex AddCommGrpCat.{u} ℕ)).map_injective
  simpa [normalizedChainIsoDoldKanN] using
    orderedKaroubiNormalizedIso_naturality F

/-! ## Pullback of cochains and their chain maps -/

@[simp]
theorem nonDegenerateSimplexEquiv_mapNonDegenerate
    (F : OrderedSimplicialMap K M) (n : ℕ)
    (x : (orderedComplexSSet K).nonDegenerate n) :
    nonDegenerateSimplexEquiv M n (F.mapNonDegenerate n x) =
      F.mapSimplex (nonDegenerateSimplexEquiv K n x) := by
  apply Subtype.ext
  exact orderedSimplexSupport_postcomp_embedding
    F.toOrderEmbedding x.1.1

/-- Pullback of an ordered cochain is precomposition by the normalized-chain
map induced by the ordered simplicial embedding. -/
theorem normalizedCochain_pullback
    (F : OrderedSimplicialMap K M) (q : ℕ) (c : Cochain M q G) :
    (SSet.normalizedChainComplexMap
        (C := AddCommGrpCat.{u}) F.toSSetMap
        (integralCoefficients : AddCommGrpCat.{u})).f q ≫
      cochainEquivNormalizedCochainHom M q c =
    cochainEquivNormalizedCochainHom K q (F.pullback q c) := by
  apply (orderedComplexSSet K).normalizedChainComplex_hom_ext
    (R := (integralCoefficients : AddCommGrpCat.{u}))
  intro x hx
  let x' : (orderedComplexSSet K).nonDegenerate q := ⟨x, hx⟩
  rw [← Category.assoc, SSet.ι_normalizedChainComplexMap_f]
  apply integralCoefficients_hom_ext
  simp only [ConcreteCategory.comp_apply]
  calc
    _ = c (nonDegenerateSimplexEquiv M q
        (F.mapNonDegenerate q x')) :=
      cochainEquivNormalizedCochainHom_nonDegenerate_generator
        M q c (F.mapNonDegenerate q x')
    _ = c (F.mapSimplex (nonDegenerateSimplexEquiv K q x')) := by
      rw [nonDegenerateSimplexEquiv_mapNonDegenerate]
    _ = F.pullback q c (nonDegenerateSimplexEquiv K q x') := rfl
    _ = _ :=
      (cochainEquivNormalizedCochainHom_nonDegenerate_generator
        K q (F.pullback q c) x').symm

/-- The disk-valued chain map represented by a cochain is contravariantly
natural for ordered simplicial embeddings. -/
theorem cochainDiskChainMap_pullback
    (F : OrderedSimplicialMap K M) (q : ℕ) (c : Cochain M q G) :
    SSet.normalizedChainComplexMap
        (C := AddCommGrpCat.{u}) F.toSSetMap
        (integralCoefficients : AddCommGrpCat.{u}) ≫
      cochainDiskChainMap M q c =
    cochainDiskChainMap K q (F.pullback q c) := by
  apply HomologicalComplex.hom_ext
  intro i
  by_cases hi : i = q + 1
  · subst i
    rw [HomologicalComplex.comp_f, cochainDiskChainMap_f_top,
      cochainDiskChainMap_f_top, ← Category.assoc,
      normalizedCochain_pullback]
    congr 2
    exact DFunLike.congr_fun (F.pullback_coboundary (G := G) q) c
  · by_cases hi' : i = q
    · subst i
      rw [HomologicalComplex.comp_f, cochainDiskChainMap_f_bottom,
        cochainDiskChainMap_f_bottom, ← Category.assoc,
        normalizedCochain_pullback]
    · exact (HomologicalComplex.isZero_double_X
        (f := 𝟙 (AddCommGrpCat.of G))
        (hi₀₁ := ComplexShape.down_mk (q + 1) q rfl)
        i hi hi').eq_of_tgt _ _

/-- The sphere-valued chain map represented by a cocycle is likewise
contravariantly natural. -/
theorem cocycleSphereChainMap_pullback
    (F : OrderedSimplicialMap K M) (q : ℕ) (c : Cochain M q G)
    (hc : coboundary M q c = 0) :
    SSet.normalizedChainComplexMap
        (C := AddCommGrpCat.{u}) F.toSSetMap
        (integralCoefficients : AddCommGrpCat.{u}) ≫
      cocycleSphereChainMap M q c hc =
    cocycleSphereChainMap K q (F.pullback q c)
      (by
        have h := LinearMap.congr_fun
          (F.pullback_coboundary (G := G) q) c
        change F.pullback (q + 1) (coboundary M q c) =
          coboundary K q (F.pullback q c) at h
        rw [← h, hc]
        simp) := by
  apply HomologicalComplex.hom_ext
  intro i
  by_cases hi : i = q
  · subst i
    rw [HomologicalComplex.comp_f, cocycleSphereChainMap_f_self,
      cocycleSphereChainMap_f_self, ← Category.assoc,
      normalizedCochain_pullback]
  · exact (HomologicalComplex.isZero_single_obj_X
      (ComplexShape.down ℕ) q (AddCommGrpCat.of G) i hi).eq_of_tgt _ _

/-! ## Naturality of the genuine Dold--Kan maps -/

@[reassoc]
theorem normalizedChainIsoDoldKanN_inv_naturality
    (F : OrderedSimplicialMap K M) :
    CategoryTheory.Abelian.DoldKan.N.map
          (freeSimplicialAbelianMap F) ≫
        (normalizedChainIsoDoldKanN (orderedComplexSSet M)).inv =
      (normalizedChainIsoDoldKanN (orderedComplexSSet K)).inv ≫
        SSet.normalizedChainComplexMap
          (C := AddCommGrpCat.{u}) F.toSSetMap
          (integralCoefficients : AddCommGrpCat.{u}) := by
  rw [← cancel_mono
    (normalizedChainIsoDoldKanN (orderedComplexSSet M)).hom]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [normalizedChainIsoDoldKanN_naturality]
  simp

/-- Denormalizing a normalized-chain map commutes with changing the ordered
simplicial source. -/
theorem denormalizeNormalizedChainMap_pullback
    (F : OrderedSimplicialMap K M)
    {C : ChainComplex AddCommGrpCat.{u} ℕ}
    (f : (orderedComplexSSet M).normalizedChainComplex
        (integralCoefficients : AddCommGrpCat.{u}) ⟶ C) :
    freeSimplicialAbelianMap F ≫
        denormalizeNormalizedChainMap (orderedComplexSSet M) f =
      denormalizeNormalizedChainMap (orderedComplexSSet K)
        (SSet.normalizedChainComplexMap
          (C := AddCommGrpCat.{u}) F.toSSetMap
          (integralCoefficients : AddCommGrpCat.{u}) ≫ f) := by
  unfold denormalizeNormalizedChainMap
  have hunit :
      freeSimplicialAbelianMap F ≫
          (CategoryTheory.Abelian.DoldKan.equivalence
            (A := AddCommGrpCat.{u})).unitIso.hom.app
              (freeSimplicialAbelian (orderedComplexSSet M)) =
        (CategoryTheory.Abelian.DoldKan.equivalence
            (A := AddCommGrpCat.{u})).unitIso.hom.app
              (freeSimplicialAbelian (orderedComplexSSet K)) ≫
          (CategoryTheory.Abelian.DoldKan.equivalence
            (A := AddCommGrpCat.{u})).inverse.map
              ((CategoryTheory.Abelian.DoldKan.equivalence
                (A := AddCommGrpCat.{u})).functor.map
                  (freeSimplicialAbelianMap F)) := by
    have hnat :=
      (CategoryTheory.Abelian.DoldKan.equivalence
        (A := AddCommGrpCat.{u})).unitIso.hom.naturality
          (freeSimplicialAbelianMap F)
    simpa only [Functor.id_obj, Functor.id_map, Functor.comp_obj,
      Functor.comp_map] using hnat
  rw [← Category.assoc, hunit]
  change
    (CategoryTheory.Abelian.DoldKan.equivalence
        (A := AddCommGrpCat.{u})).unitIso.hom.app
          (freeSimplicialAbelian (orderedComplexSSet K)) ≫
      CategoryTheory.Abelian.DoldKan.Γ.map
        (CategoryTheory.Abelian.DoldKan.N.map
          (freeSimplicialAbelianMap F)) ≫
      CategoryTheory.Abelian.DoldKan.Γ.map
        ((normalizedChainIsoDoldKanN (orderedComplexSSet M)).inv ≫ f) = _
  simp only [Category.assoc, ← Functor.map_comp]
  rw [normalizedChainIsoDoldKanN_inv_naturality_assoc]

/-- The generator inclusion into the degreewise free abelian group is
natural for ordered simplicial embeddings. -/
theorem freeSimplicialAbelianGenerator_naturality
    (F : OrderedSimplicialMap K M) :
    F.toSSetMap ≫ freeSimplicialAbelianGenerator (orderedComplexSSet M) =
      freeSimplicialAbelianGenerator (orderedComplexSSet K) ≫
        Functor.whiskerRight (freeSimplicialAbelianMap F)
          (forget AddCommGrpCat.{u}) := by
  ext Δ x
  change
    (Limits.Sigma.ι
      (fun _ : (orderedComplexSSet M).obj Δ =>
        (integralCoefficients : AddCommGrpCat.{u}))
      (F.toSSetMap.app Δ x)) (ULift.up (1 : ℤ)) =
    (freeSimplicialAbelianMap F).app Δ
      ((Limits.Sigma.ι
        (fun _ : (orderedComplexSSet K).obj Δ =>
          (integralCoefficients : AddCommGrpCat.{u})) x)
        (ULift.up (1 : ℤ)))
  exact (CategoryTheory.congr_fun
    (Limits.Sigma.ι_comp_map'
      (f := fun _ : (orderedComplexSSet K).obj Δ =>
        (integralCoefficients : AddCommGrpCat.{u}))
      (g := fun _ : (orderedComplexSSet M).obj Δ =>
        (integralCoefficients : AddCommGrpCat.{u}))
      (fun y => F.toSSetMap.app Δ y) (fun _ => 𝟙 _) x)
    (ULift.up (1 : ℤ))).symm

/-- The genuine simplicial map associated with a normalized-chain map is
contravariantly natural in the ordered source. -/
theorem simplicialMapOfNormalizedChainMap_pullback
    (F : OrderedSimplicialMap K M)
    {C : ChainComplex AddCommGrpCat.{u} ℕ}
    (f : (orderedComplexSSet M).normalizedChainComplex
        (integralCoefficients : AddCommGrpCat.{u}) ⟶ C) :
    F.toSSetMap ≫
        simplicialMapOfNormalizedChainMap (orderedComplexSSet M) f =
      simplicialMapOfNormalizedChainMap (orderedComplexSSet K)
        (SSet.normalizedChainComplexMap
          (C := AddCommGrpCat.{u}) F.toSSetMap
          (integralCoefficients : AddCommGrpCat.{u}) ≫ f) := by
  unfold simplicialMapOfNormalizedChainMap
  rw [← Category.assoc,
    freeSimplicialAbelianGenerator_naturality]
  calc
    _ = freeSimplicialAbelianGenerator (orderedComplexSSet K) ≫
        Functor.whiskerRight
          (freeSimplicialAbelianMap F ≫
            denormalizeNormalizedChainMap (orderedComplexSSet M) f)
          (forget AddCommGrpCat.{u}) := rfl
    _ = _ := by rw [denormalizeNormalizedChainMap_pullback]

/-- Genuine `L`-valued cochain maps commute with ordered pullback. -/
theorem cochainToLMap_pullback
    (F : OrderedSimplicialMap K M) (q : ℕ) (c : Cochain M q G) :
    F.toSSetMap ≫ cochainToLMap M q c =
      cochainToLMap K q (F.pullback q c) := by
  unfold cochainToLMap
  rw [simplicialMapOfNormalizedChainMap_pullback,
    cochainDiskChainMap_pullback]

/-- Genuine `K`-valued cocycle maps commute with ordered pullback. -/
theorem cocycleToKMap_pullback
    (F : OrderedSimplicialMap K M) (q : ℕ) (c : Cochain M q G)
    (hc : coboundary M q c = 0) :
    F.toSSetMap ≫ cocycleToKMap M q c hc =
      cocycleToKMap K q (F.pullback q c)
        (by
          have h := LinearMap.congr_fun
            (F.pullback_coboundary (G := G) q) c
          change F.pullback (q + 1) (coboundary M q c) =
            coboundary K q (F.pullback q c) at h
          rw [← h, hc]
          simp) := by
  unfold cocycleToKMap
  rw [simplicialMapOfNormalizedChainMap_pullback,
    cocycleSphereChainMap_pullback]

end GeneralSphereT.SimplicialCochain
