import Formalization.Section4CochainDoldKanChainMaps
import Formalization.Section4DoldKanCochainBridge
import Formalization.Section4RelativeMappingGroups

set_option linter.style.header false

/-!
# Section 4: from normalized-chain maps to genuine simplicial maps

The free simplicial abelian group on a simplicial set has, as its split
nondegenerate complex, the normalized integral chains used in the paper.
The comparison between that split complex and the normalized Moore complex,
followed by the unit of the Dold--Kan equivalence, turns a normalized-chain
map into an actual map of simplicial sets to `Γ C`.
-/

noncomputable section

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits Opposite Simplicial
open AlgebraicTopology.DoldKan

namespace GeneralSphereT.SimplicialCochain

universe u

/-- The degreewise free abelian group on a simplicial set, with our
universe-polymorphic copy of `ℤ` as generator object. -/
abbrev freeSimplicialAbelian (X : SSet.{u}) :
    SimplicialObject AddCommGrpCat.{u} :=
  ((SimplicialObject.whiskering _ _).obj
    (sigmaConst.obj integralCoefficients)).obj X

/-- For a free simplicial abelian group, Mathlib's split nondegenerate
complex is canonically isomorphic to its normalized Moore complex. -/
def normalizedChainIsoDoldKanN (X : SSet.{u}) :
    X.normalizedChainComplex integralCoefficients ≅
      CategoryTheory.Abelian.DoldKan.N.obj (freeSimplicialAbelian X) :=
  (CategoryTheory.Idempotents.toKaroubi
      (ChainComplex AddCommGrpCat.{u} ℕ)).preimageIso
    ((X.splitting.map
        (sigmaConst.obj integralCoefficients)).toKaroubiNondegComplexIsoN₁ ≪≫
      (N₁_iso_normalizedMooreComplex_comp_toKaroubi
        AddCommGrpCat.{u}).app (freeSimplicialAbelian X))

/-- Apply Dold--Kan to a map defined on normalized chains. -/
def denormalizeNormalizedChainMap
    (X : SSet.{u}) {C : ChainComplex AddCommGrpCat.{u} ℕ}
    (f : X.normalizedChainComplex integralCoefficients ⟶ C) :
    freeSimplicialAbelian X ⟶
      CategoryTheory.Abelian.DoldKan.Γ.obj C :=
  (CategoryTheory.Abelian.DoldKan.equivalence
      (A := AddCommGrpCat.{u})).unitIso.hom.app (freeSimplicialAbelian X) ≫
    CategoryTheory.Abelian.DoldKan.Γ.map
      ((normalizedChainIsoDoldKanN X).inv ≫ f)

/-- The generator inclusion of a simplicial set into its degreewise free
abelian group. -/
def freeSimplicialAbelianGenerator (X : SSet.{u}) :
    X ⟶ GeneralSphereT.Section4.underlyingSSet
      (freeSimplicialAbelian X) where
  app Δ := ↾fun x =>
    (Sigma.ι (fun _ : X.obj Δ => integralCoefficients) x)
      (ULift.up (1 : ℤ))
  naturality Δ Δ' θ := by
    ext x
    exact (CategoryTheory.congr_fun
      (Sigma.ι_comp_map'
        (f := fun _ : X.obj Δ => integralCoefficients)
        (g := fun _ : X.obj Δ' => integralCoefficients)
        (fun y : X.obj Δ => X.map θ y)
        (fun _ => 𝟙 integralCoefficients) x)
      (ULift.up (1 : ℤ))).symm

/-- A normalized-chain map gives a genuine simplicial-set map to the
underlying simplicial set of its Dold--Kan denormalization. -/
def simplicialMapOfNormalizedChainMap
    (X : SSet.{u}) {C : ChainComplex AddCommGrpCat.{u} ℕ}
    (f : X.normalizedChainComplex integralCoefficients ⟶ C) :
    X ⟶ GeneralSphereT.Section4.underlyingSSet
      (CategoryTheory.Abelian.DoldKan.Γ.obj C) :=
  freeSimplicialAbelianGenerator X ≫
    Functor.whiskerRight (denormalizeNormalizedChainMap X f)
      (forget AddCommGrpCat.{u})

set_option backward.isDefEq.respectTransparency false

@[simp]
theorem doldKanGamma_map_zero
    {C D : ChainComplex AddCommGrpCat.{u} ℕ} :
    CategoryTheory.Abelian.DoldKan.Γ.map (0 : C ⟶ D) = 0 := by
  apply NatTrans.ext
  funext Δ
  apply (Γ₀.splitting C).hom_ext'
  intro A
  rw [StandardModels.denormalize_map_on_summand]
  simp

theorem doldKanGamma_map_add
    {C D : ChainComplex AddCommGrpCat.{u} ℕ} (f g : C ⟶ D) :
    CategoryTheory.Abelian.DoldKan.Γ.map (f + g) =
      CategoryTheory.Abelian.DoldKan.Γ.map f +
        CategoryTheory.Abelian.DoldKan.Γ.map g := by
  apply NatTrans.ext
  funext Δ
  apply (Γ₀.splitting C).hom_ext'
  intro A
  rw [StandardModels.denormalize_map_on_summand]
  change (f.f A.1.unop.len + g.f A.1.unop.len) ≫
      ((Γ₀.splitting D).cofan Δ).inj A =
    ((Γ₀.splitting C).cofan Δ).inj A ≫
      ((CategoryTheory.Abelian.DoldKan.Γ.map f).app Δ +
        (CategoryTheory.Abelian.DoldKan.Γ.map g).app Δ)
  rw [Preadditive.add_comp, Preadditive.comp_add,
    StandardModels.denormalize_map_on_summand,
    StandardModels.denormalize_map_on_summand]

theorem denormalizeNormalizedChainMap_comp
    (X : SSet.{u}) {C D : ChainComplex AddCommGrpCat.{u} ℕ}
    (f : X.normalizedChainComplex integralCoefficients ⟶ C)
    (g : C ⟶ D) :
    denormalizeNormalizedChainMap X (f ≫ g) =
      denormalizeNormalizedChainMap X f ≫
        CategoryTheory.Abelian.DoldKan.Γ.map g := by
  unfold denormalizeNormalizedChainMap
  rw [Category.assoc, ← Functor.map_comp]
  rfl

theorem simplicialMapOfNormalizedChainMap_comp
    (X : SSet.{u}) {C D : ChainComplex AddCommGrpCat.{u} ℕ}
    (f : X.normalizedChainComplex integralCoefficients ⟶ C)
    (g : C ⟶ D) :
    simplicialMapOfNormalizedChainMap X (f ≫ g) =
      simplicialMapOfNormalizedChainMap X f ≫
        Functor.whiskerRight
          (CategoryTheory.Abelian.DoldKan.Γ.map g)
          (forget AddCommGrpCat.{u}) := by
  simp [simplicialMapOfNormalizedChainMap,
    denormalizeNormalizedChainMap_comp, Category.assoc]

@[simp]
theorem denormalizeNormalizedChainMap_zero
    (X : SSet.{u}) {C : ChainComplex AddCommGrpCat.{u} ℕ} :
    denormalizeNormalizedChainMap X
        (0 : X.normalizedChainComplex integralCoefficients ⟶ C) = 0 := by
  unfold denormalizeNormalizedChainMap
  rw [comp_zero, doldKanGamma_map_zero, comp_zero]

theorem denormalizeNormalizedChainMap_add
    (X : SSet.{u}) {C : ChainComplex AddCommGrpCat.{u} ℕ}
    (f g : X.normalizedChainComplex integralCoefficients ⟶ C) :
    denormalizeNormalizedChainMap X (f + g) =
      denormalizeNormalizedChainMap X f +
        denormalizeNormalizedChainMap X g := by
  unfold denormalizeNormalizedChainMap
  rw [Preadditive.comp_add, doldKanGamma_map_add, Preadditive.comp_add]

@[simp]
theorem simplicialMapOfNormalizedChainMap_zero
    (X : SSet.{u}) {C : ChainComplex AddCommGrpCat.{u} ℕ} :
    simplicialMapOfNormalizedChainMap X
        (0 : X.normalizedChainComplex integralCoefficients ⟶ C) = 0 := by
  unfold simplicialMapOfNormalizedChainMap
  rw [denormalizeNormalizedChainMap_zero]
  rfl

theorem simplicialMapOfNormalizedChainMap_add
    (X : SSet.{u}) {C : ChainComplex AddCommGrpCat.{u} ℕ}
    (f g : X.normalizedChainComplex integralCoefficients ⟶ C) :
    simplicialMapOfNormalizedChainMap X (f + g) =
      simplicialMapOfNormalizedChainMap X f +
        simplicialMapOfNormalizedChainMap X g := by
  unfold simplicialMapOfNormalizedChainMap
  rw [denormalizeNormalizedChainMap_add]
  rfl

/-- Pointwise naturality with the source and simplicial abelian target made
explicit.  This small wrapper avoids expensive reconstruction of those
parameters when the displayed map itself contains a Dold--Kan unit. -/
theorem underlyingSSetMap_naturality_apply
    {X : SSet.{u}} {A : SimplicialObject AddCommGrpCat.{u}}
    (f : X ⟶ GeneralSphereT.Section4.underlyingSSet A)
    {Δ Δ' : SimplexCategoryᵒᵖ} (θ : Δ ⟶ Δ') (x : X.obj Δ) :
    f.app Δ' (X.map θ x) =
      (GeneralSphereT.Section4.underlyingSSet A).map θ (f.app Δ x) := by
  exact f.naturality_apply θ x

variable {V G : Type u} [LinearOrder V] [Fintype V] [AddCommGroup G]

/-- The genuine `L(G,q+1)`-valued simplicial map represented by a
degree-`q` cochain. -/
def cochainToLMap
    (M : AbstractSimplicialComplex V) (q : ℕ) (c : Cochain M q G) :
    orderedComplexSSet M ⟶
      GeneralSphereT.Section4.underlyingSSet
        (StandardModels.L (AddCommGrpCat.of G) (q + 1)) :=
  simplicialMapOfNormalizedChainMap (orderedComplexSSet M)
    (cochainDiskChainMap M q c)

set_option maxHeartbeats 800000 in
/-- Pointwise naturality of the genuine `L`-valued map.  Recording it next
to the definition prevents downstream files from repeatedly unfolding the
Dold--Kan unit merely to use the naturality field of this map. -/
theorem cochainToLMap_naturality_apply
    (M : AbstractSimplicialComplex V) (q : ℕ) (c : Cochain M q G)
    {Δ Δ' : SimplexCategoryᵒᵖ} (θ : Δ ⟶ Δ')
    (x : (orderedComplexSSet M).obj Δ) :
    (cochainToLMap M q c).app Δ'
        ((orderedComplexSSet M).map θ x) =
      (GeneralSphereT.Section4.underlyingSSet
          (StandardModels.L (AddCommGrpCat.of G) (q + 1))).map θ
        ((cochainToLMap M q c).app Δ x) := by
  exact underlyingSSetMap_naturality_apply
    (X := orderedComplexSSet M)
    (A := StandardModels.L (AddCommGrpCat.of G) (q + 1))
    (cochainToLMap M q c) θ x

/-- The genuine `K(G,q)`-valued simplicial map represented by a cocycle. -/
def cocycleToKMap
    (M : AbstractSimplicialComplex V) (q : ℕ)
    (c : Cochain M q G) (hc : coboundary M q c = 0) :
    orderedComplexSSet M ⟶
      GeneralSphereT.Section4.underlyingSSet
        (StandardModels.K (AddCommGrpCat.of G) q) :=
  simplicialMapOfNormalizedChainMap (orderedComplexSSet M)
    (cocycleSphereChainMap M q c hc)

@[simp]
theorem cochainToLMap_zero
    (M : AbstractSimplicialComplex V) (q : ℕ) :
    cochainToLMap (G := G) M q 0 = 0 := by
  unfold cochainToLMap
  rw [cochainDiskChainMap_zero,
    simplicialMapOfNormalizedChainMap_zero]

theorem cochainToLMap_add
    (M : AbstractSimplicialComplex V) (q : ℕ)
    (c c' : Cochain M q G) :
    cochainToLMap M q (c + c') =
      cochainToLMap M q c + cochainToLMap M q c' := by
  unfold cochainToLMap
  rw [cochainDiskChainMap_add,
    simplicialMapOfNormalizedChainMap_add]

/-- Postcomposition of the genuine `L`-valued map with the standard
`d : L → K` is exactly the genuine map represented by the coboundary. -/
theorem cochainToLMap_comp_d
    (M : AbstractSimplicialComplex V) (q : ℕ) (c : Cochain M q G) :
    cochainToLMap M q c ≫
        Functor.whiskerRight
          (StandardModels.d (AddCommGrpCat.of G) (q + 1))
          (forget AddCommGrpCat.{u}) =
      cocycleToKMap M (q + 1) (coboundary M q c)
        (coboundary_coboundary M q c) := by
  change simplicialMapOfNormalizedChainMap (orderedComplexSSet M)
      (cochainDiskChainMap M q c) ≫
        Functor.whiskerRight
          (CategoryTheory.Abelian.DoldKan.Γ.map
            (StandardModels.diskToSphereSucc (AddCommGrpCat.of G) q))
          (forget AddCommGrpCat.{u}) = _
  rw [← simplicialMapOfNormalizedChainMap_comp]
  rw [cochainDiskChainMap_comp_diskToSphere]
  rfl

set_option maxHeartbeats 2000000 in
-- Specializing the Dold--Kan natural transformation at a simplex is costly
-- if every downstream caller has to elaborate the categorical composite.
/-- Pointwise form of `cochainToLMap_comp_d`. -/
theorem cochainToLMap_comp_d_apply
    (M : AbstractSimplicialComplex V) (q : ℕ) (c : Cochain M q G)
    (Δ : SimplexCategoryᵒᵖ) (x : (orderedComplexSSet M).obj Δ) :
    (StandardModels.d (AddCommGrpCat.of G) (q + 1)).app Δ
        ((cochainToLMap M q c).app Δ x) =
      (cocycleToKMap M (q + 1) (coboundary M q c)
        (coboundary_coboundary M q c)).app Δ x := by
  change ((simplicialMapOfNormalizedChainMap (orderedComplexSSet M)
      (cochainDiskChainMap M q c) ≫
        Functor.whiskerRight
          (CategoryTheory.Abelian.DoldKan.Γ.map
            (StandardModels.diskToSphereSucc (AddCommGrpCat.of G) q))
          (forget AddCommGrpCat.{u})).app Δ) x =
    (simplicialMapOfNormalizedChainMap (orderedComplexSSet M)
      (cocycleSphereChainMap M (q + 1) (coboundary M q c)
        (coboundary_coboundary M q c))).app Δ x
  rw [← simplicialMapOfNormalizedChainMap_comp]
  rw [cochainDiskChainMap_comp_diskToSphere]

end GeneralSphereT.SimplicialCochain
