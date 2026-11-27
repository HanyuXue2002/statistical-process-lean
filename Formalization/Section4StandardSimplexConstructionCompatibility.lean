import Formalization.Section4NormalizedChainDoldKanMap
import Formalization.Section4StandardSimplexLClassification
import Formalization.Section4StandardSimplexKClassification

set_option linter.style.header false

/-!
# Section 4: compatibility of the two standard-simplex constructions

The global construction first turns a cochain into a normalized-chain map and
then applies Dold--Kan.  The coordinate construction describes the resulting
simplex through epimorphism/anchored-face coordinates.

Mathlib's Dold--Kan unit is implemented as the inverse of a composite
categorical isomorphism, so its pointwise coordinate formula is intentionally
not unfolded here.  Instead this file proves the invariant statement needed by
the paper:

* evaluation of the global construction on the canonical top simplex is an
  additive equivalence, both for `L` and for `K`;
* hence the global and coordinate classifications differ by explicit additive
  automorphisms of the standard-model levels;
* these two comparison automorphisms commute with the genuine simplicial map
  `d : L(G,q+1) ⟶ K(G,q+1)`.

Thus no unproved identification of two concrete implementations of Dold--Kan
is used.
-/

noncomputable section

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits Opposite
  SimplexCategory Simplicial
open AlgebraicTopology.DoldKan

namespace GeneralSphereT

namespace SimplicialCochain

open DoldKanExplicitBridge

universe u

/-- The identity vertex string, regarded as the canonical top-dimensional
simplex of the ordered-complex model of `Δⁿ`. -/
def standardSimplexTop (n : ℕ) :
    (orderedComplexSSet (standardSimplex n)).obj (op ⦋n⦌) :=
  ⟨OrderHom.id, by
    change (orderedSimplexSupport (OrderHom.id :
      Fin (n + 1) →o Fin (n + 1))).Nonempty
    exact Finset.image_nonempty.mpr Finset.univ_nonempty⟩

@[simp]
theorem standardSimplexTop_apply (n : ℕ) (i : Fin (n + 1)) :
    (standardSimplexTop n).1 i = i :=
  rfl

/-- The simplex `x` of `Δⁿ` is the image of the canonical top simplex under
its vertex-string morphism. -/
def standardSimplexHom (n : ℕ) {Δ : SimplexCategoryᵒᵖ}
    (x : (orderedComplexSSet (standardSimplex n)).obj Δ) :
    Δ.unop ⟶ ⦋n⦌ :=
  SimplexCategory.Hom.mk x.1

@[simp]
theorem standardSimplexHom_top (n : ℕ) :
    standardSimplexHom n (standardSimplexTop n) = 𝟙 ⦋n⦌ := by
  ext i
  rfl

@[simp]
theorem standardSimplex_map_hom_top (n : ℕ) {Δ : SimplexCategoryᵒᵖ}
    (x : (orderedComplexSSet (standardSimplex n)).obj Δ) :
    (orderedComplexSSet (standardSimplex n)).map
        (standardSimplexHom n x).op (standardSimplexTop n) = x := by
  apply Subtype.ext
  apply OrderHom.ext
  funext i
  rfl

/-- A map out of the free simplicial abelian group on `Δⁿ`, constructed from
the prescribed value of its canonical top generator. -/
def standardSimplexFreeLift (n : ℕ) (A : SimplicialObject AddCommGrpCat)
    (y : A.obj (op ⦋n⦌)) :
    freeSimplicialAbelian (orderedComplexSSet (standardSimplex n)) ⟶ A where
  app Δ := Limits.Sigma.desc fun x =>
    integerGeneratorHom (A.map (standardSimplexHom n x).op y)
  naturality Δ Δ' θ := by
    apply Limits.Sigma.hom_ext
    intro x
    apply integralCoefficients_hom_ext
    simp only [ConcreteCategory.comp_apply]
    have hg :
        (freeSimplicialAbelian (orderedComplexSSet (standardSimplex n))).map θ
          ((Sigma.ι (fun _ : (orderedComplexSSet (standardSimplex n)).obj Δ =>
            integralCoefficients) x) (ULift.up (1 : ℤ))) =
        (Sigma.ι (fun _ : (orderedComplexSSet (standardSimplex n)).obj Δ' =>
            integralCoefficients)
          ((orderedComplexSSet (standardSimplex n)).map θ x))
            (ULift.up (1 : ℤ)) := by
      symm
      exact ConcreteCategory.congr_hom
        ((freeSimplicialAbelianGenerator
          (orderedComplexSSet (standardSimplex n))).naturality θ) x
    rw [hg]
    have hdesc' :
        (Limits.Sigma.desc
          (fun z : (orderedComplexSSet (standardSimplex n)).obj Δ' =>
            integerGeneratorHom (A.map (standardSimplexHom n z).op y)))
          ((Sigma.ι (fun _ : (orderedComplexSSet (standardSimplex n)).obj Δ' =>
              integralCoefficients)
            ((orderedComplexSSet (standardSimplex n)).map θ x))
              (ULift.up (1 : ℤ))) =
          A.map (standardSimplexHom n
            ((orderedComplexSSet (standardSimplex n)).map θ x)).op y := by
      exact (CategoryTheory.congr_fun
        (Limits.Sigma.ι_desc
          (fun z : (orderedComplexSSet (standardSimplex n)).obj Δ' =>
            integerGeneratorHom (A.map (standardSimplexHom n z).op y))
          ((orderedComplexSSet (standardSimplex n)).map θ x))
        (ULift.up (1 : ℤ))).trans
          (integerGeneratorHom_one _)
    have hdesc :
        (Limits.Sigma.desc
          (fun z : (orderedComplexSSet (standardSimplex n)).obj Δ =>
            integerGeneratorHom (A.map (standardSimplexHom n z).op y)))
          ((Sigma.ι (fun _ : (orderedComplexSSet (standardSimplex n)).obj Δ =>
              integralCoefficients) x) (ULift.up (1 : ℤ))) =
          A.map (standardSimplexHom n x).op y := by
      exact (CategoryTheory.congr_fun
        (Limits.Sigma.ι_desc
          (fun z : (orderedComplexSSet (standardSimplex n)).obj Δ =>
            integerGeneratorHom (A.map (standardSimplexHom n z).op y)) x)
        (ULift.up (1 : ℤ))).trans
          (integerGeneratorHom_one _)
    rw [hdesc', hdesc]
    change A.map (standardSimplexHom n
        ((orderedComplexSSet (standardSimplex n)).map θ x)).op y =
      A.map θ (A.map (standardSimplexHom n x).op y)
    rw [← ConcreteCategory.comp_apply, ← A.map_comp]
    rfl

/-- The canonical basis element indexed by the top simplex. -/
def standardSimplexTopGenerator (n : ℕ) :
    (freeSimplicialAbelian (orderedComplexSSet (standardSimplex n))).obj
      (op ⦋n⦌) :=
  (Sigma.ι (fun _ : (orderedComplexSSet (standardSimplex n)).obj
    (op ⦋n⦌) => integralCoefficients) (standardSimplexTop n))
      (ULift.up (1 : ℤ))

@[simp]
theorem standardSimplexFreeLift_eval_top (n : ℕ)
    (A : SimplicialObject AddCommGrpCat) (y : A.obj (op ⦋n⦌)) :
    (standardSimplexFreeLift n A y).app (op ⦋n⦌)
      (standardSimplexTopGenerator n) = y := by
  simpa [standardSimplexTopGenerator, standardSimplexFreeLift] using
    integerGeneratorHom_one y

/-- Evaluation on the canonical top generator. -/
def standardFreeMapTopValue (n : ℕ) (A : SimplicialObject AddCommGrpCat) :
    (freeSimplicialAbelian (orderedComplexSSet (standardSimplex n)) ⟶ A) →+
      A.obj (op ⦋n⦌) where
  toFun f := f.app (op ⦋n⦌) (standardSimplexTopGenerator n)
  map_zero' := rfl
  map_add' _ _ := rfl

@[simp]
theorem standardFreeMapTopValue_freeLift (n : ℕ)
    (A : SimplicialObject AddCommGrpCat) (y : A.obj (op ⦋n⦌)) :
    standardFreeMapTopValue n A (standardSimplexFreeLift n A y) = y := by
  exact standardSimplexFreeLift_eval_top n A y

theorem standardSimplexFreeLift_freeMapTopValue (n : ℕ)
    (A : SimplicialObject AddCommGrpCat)
    (f : freeSimplicialAbelian (orderedComplexSSet (standardSimplex n)) ⟶ A) :
    standardSimplexFreeLift n A (standardFreeMapTopValue n A f) = f := by
  apply NatTrans.ext
  funext Δ
  apply Limits.Sigma.hom_ext
  intro x
  apply integralCoefficients_hom_ext
  let θ : op ⦋n⦌ ⟶ Δ := (standardSimplexHom n x).op
  have hg :
      (freeSimplicialAbelian (orderedComplexSSet (standardSimplex n))).map θ
          (standardSimplexTopGenerator n) =
        (Sigma.ι (fun _ : (orderedComplexSSet (standardSimplex n)).obj Δ =>
          integralCoefficients) x) (ULift.up (1 : ℤ)) := by
    have h := ConcreteCategory.congr_hom
      ((freeSimplicialAbelianGenerator
        (orderedComplexSSet (standardSimplex n))).naturality θ)
          (standardSimplexTop n)
    symm at h
    simp only [ConcreteCategory.comp_apply] at h
    change
      (freeSimplicialAbelian (orderedComplexSSet (standardSimplex n))).map θ
          (standardSimplexTopGenerator n) =
        (Sigma.ι (fun _ : (orderedComplexSSet (standardSimplex n)).obj Δ =>
          integralCoefficients)
          ((orderedComplexSSet (standardSimplex n)).map θ
            (standardSimplexTop n))) (ULift.up (1 : ℤ)) at h
    have hx : (orderedComplexSSet (standardSimplex n)).map θ
        (standardSimplexTop n) = x :=
      standardSimplex_map_hom_top n x
    rw [hx] at h
    exact h
  have hnat := ConcreteCategory.congr_hom (f.naturality θ)
    (standardSimplexTopGenerator n)
  have hnat' :
      f.app Δ
          ((Sigma.ι (fun _ : (orderedComplexSSet (standardSimplex n)).obj Δ =>
            integralCoefficients) x) (ULift.up (1 : ℤ))) =
        A.map θ (f.app (op ⦋n⦌) (standardSimplexTopGenerator n)) := by
    simpa only [ConcreteCategory.comp_apply, hg] using hnat
  change (standardSimplexFreeLift n A (standardFreeMapTopValue n A f)).app Δ
      ((Sigma.ι (fun _ : (orderedComplexSSet (standardSimplex n)).obj Δ =>
        integralCoefficients) x) (ULift.up (1 : ℤ))) = _
  have hdesc :
      (standardSimplexFreeLift n A (standardFreeMapTopValue n A f)).app Δ
          ((Sigma.ι (fun _ : (orderedComplexSSet (standardSimplex n)).obj Δ =>
            integralCoefficients) x) (ULift.up (1 : ℤ))) =
        A.map θ (standardFreeMapTopValue n A f) := by
    exact (CategoryTheory.congr_fun
      (Limits.Sigma.ι_desc
        (fun z : (orderedComplexSSet (standardSimplex n)).obj Δ =>
          integerGeneratorHom
            (A.map (standardSimplexHom n z).op
              (standardFreeMapTopValue n A f))) x)
      (ULift.up (1 : ℤ))).trans (integerGeneratorHom_one _)
  rw [hdesc]
  exact hnat'.symm

/-- Maps out of the free simplicial abelian group on `Δⁿ` are classified by
the value on its top generator. -/
def standardFreeMapTopEquiv (n : ℕ) (A : SimplicialObject AddCommGrpCat) :
    (freeSimplicialAbelian (orderedComplexSSet (standardSimplex n)) ⟶ A) ≃+
      A.obj (op ⦋n⦌) :=
  AddEquiv.ofBijective (standardFreeMapTopValue n A)
    ⟨fun f g h => by
        rw [← standardSimplexFreeLift_freeMapTopValue n A f,
          ← standardSimplexFreeLift_freeMapTopValue n A g, h],
      fun y =>
        ⟨standardSimplexFreeLift n A y,
          standardFreeMapTopValue_freeLift n A y⟩⟩

/-- Dold--Kan denormalization induces a bijection on maps out of a normalized
free simplicial chain complex. -/
theorem denormalizeNormalizedChainMap_bijective
    (X : SSet.{u}) (C : ChainComplex AddCommGrpCat.{u} ℕ) :
    Function.Bijective (denormalizeNormalizedChainMap X (C := C)) := by
  let e := CategoryTheory.Abelian.DoldKan.equivalence
    (A := AddCommGrpCat.{u})
  have h₁ : Function.Bijective
      (fun f : X.normalizedChainComplex integralCoefficients ⟶ C =>
        (normalizedChainIsoDoldKanN X).inv ≫ f) := by
    convert
      ((Iso.homCongr (normalizedChainIsoDoldKanN X) (Iso.refl C)).bijective)
        using 1
    funext f
    simp only [Iso.homCongr_apply, Iso.refl_hom, Category.comp_id]
  have h₂ : Function.Bijective
      (fun f : e.functor.obj (freeSimplicialAbelian X) ⟶ C =>
        e.unitIso.hom.app (freeSimplicialAbelian X) ≫ e.inverse.map f) := by
    convert ((e.toAdjunction.homEquiv
      (freeSimplicialAbelian X) C).bijective) using 1
    · rfl
    · funext f
      rw [Adjunction.homEquiv_apply]
      rfl
  change Function.Bijective
    ((fun f : e.functor.obj (freeSimplicialAbelian X) ⟶ C =>
        e.unitIso.hom.app (freeSimplicialAbelian X) ≫ e.inverse.map f) ∘
      fun f : X.normalizedChainComplex integralCoefficients ⟶ C =>
        (normalizedChainIsoDoldKanN X).inv ≫ f)
  exact h₂.comp h₁

def denormalizeNormalizedChainMapAddHom
    (X : SSet.{u}) (C : ChainComplex AddCommGrpCat.{u} ℕ) :
    (X.normalizedChainComplex integralCoefficients ⟶ C) →+
      (freeSimplicialAbelian X ⟶
        CategoryTheory.Abelian.DoldKan.Γ.obj C) where
  toFun := denormalizeNormalizedChainMap X
  map_zero' := denormalizeNormalizedChainMap_zero X
  map_add' := denormalizeNormalizedChainMap_add X

/-- Additive form of Dold--Kan full faithfulness for the maps used here. -/
def denormalizeNormalizedChainMapEquiv
    (X : SSet.{u}) (C : ChainComplex AddCommGrpCat.{u} ℕ) :
    (X.normalizedChainComplex integralCoefficients ⟶ C) ≃+
      (freeSimplicialAbelian X ⟶
        CategoryTheory.Abelian.DoldKan.Γ.obj C) :=
  AddEquiv.ofBijective (denormalizeNormalizedChainMapAddHom X C)
    (denormalizeNormalizedChainMap_bijective X C)

variable {G : Type} [AddCommGroup G]

/-- A chain map to the two-term disk is uniquely its bottom-degree cochain. -/
theorem cochainDiskChainMap_injective
    {V : Type} [LinearOrder V] [Fintype V]
    (M : AbstractSimplicialComplex V) (q : ℕ) :
    Function.Injective (cochainDiskChainMap (G := G) M q) := by
  intro c c' h
  apply (cochainEquivNormalizedCochainHom M q).injective
  rw [← cancel_mono
    (HomologicalComplex.doubleXIso₁ (𝟙 (AddCommGrpCat.of G))
      (ComplexShape.down_mk (q + 1) q rfl) (by omega)).inv]
  simpa only [cochainDiskChainMap_f_bottom] using
    HomologicalComplex.congr_hom h q

theorem cochainDiskChainMap_surjective
    {V : Type} [LinearOrder V] [Fintype V]
    (M : AbstractSimplicialComplex V) (q : ℕ) :
    Function.Surjective (cochainDiskChainMap (G := G) M q) := by
  intro F
  let e₀ := HomologicalComplex.doubleXIso₀ (𝟙 (AddCommGrpCat.of G))
    (ComplexShape.down_mk (q + 1) q rfl)
  let e₁ := HomologicalComplex.doubleXIso₁ (𝟙 (AddCommGrpCat.of G))
    (ComplexShape.down_mk (q + 1) q rfl) (by omega)
  let φ : NormalizedCochainHom (G := G) M q := F.f q ≫ e₁.hom
  let c : Cochain M q G := (cochainEquivNormalizedCochainHom M q).symm φ
  refine ⟨c, ?_⟩
  apply HomologicalComplex.to_double_hom_ext
  · rw [cochainDiskChainMap_f_top]
    rw [cochainEquivNormalizedCochainHom_coboundary]
    have hc : cochainEquivNormalizedCochainHom M q c = F.f q ≫ e₁.hom := by
      simp [c, φ]
    rw [hc, ← Category.assoc]
    rw [← F.comm (q + 1) q]
    rw [HomologicalComplex.double_d]
    · simp [e₁, Category.assoc]
    · omega
  · rw [cochainDiskChainMap_f_bottom]
    have hc : cochainEquivNormalizedCochainHom M q c = F.f q ≫ e₁.hom := by
      simp [c, φ]
    rw [hc]
    simp [e₁, Category.assoc]

theorem cochainDiskChainMap_bijective
    {V : Type} [LinearOrder V] [Fintype V]
    (M : AbstractSimplicialComplex V) (q : ℕ) :
    Function.Bijective (cochainDiskChainMap (G := G) M q) :=
  ⟨cochainDiskChainMap_injective M q,
    cochainDiskChainMap_surjective M q⟩

def cochainDiskChainMapAddHom
    {V : Type} [LinearOrder V] [Fintype V]
    (M : AbstractSimplicialComplex V) (q : ℕ) :
    Cochain M q G →+
      ((orderedComplexSSet M).normalizedChainComplex integralCoefficients ⟶
        StandardModels.diskComplex (AddCommGrpCat.of G) (q + 1)) where
  toFun := cochainDiskChainMap M q
  map_zero' := cochainDiskChainMap_zero M q
  map_add' := cochainDiskChainMap_add M q

/-- Cochains are exactly the normalized-chain maps into the two-term disk. -/
def cochainDiskChainMapEquiv
    {V : Type} [LinearOrder V] [Fintype V]
    (M : AbstractSimplicialComplex V) (q : ℕ) :
    Cochain M q G ≃+
      ((orderedComplexSSet M).normalizedChainComplex integralCoefficients ⟶
        StandardModels.diskComplex (AddCommGrpCat.of G) (q + 1)) :=
  AddEquiv.ofBijective (cochainDiskChainMapAddHom M q)
    (cochainDiskChainMap_bijective M q)

/-- A cocycle, bundled as an element of the kernel, gives a chain map to the
one-term sphere complex. -/
def cocycleSphereChainMapSubtype
    {V : Type} [LinearOrder V] [Fintype V]
    (M : AbstractSimplicialComplex V) (q : ℕ)
    (z : LinearMap.ker (coboundary (G := G) M q)) :
    (orderedComplexSSet M).normalizedChainComplex integralCoefficients ⟶
      StandardModels.sphereComplex (AddCommGrpCat.of G) q :=
  cocycleSphereChainMap M q z.1 (LinearMap.mem_ker.mp z.2)

theorem cocycleSphereChainMapSubtype_injective
    {V : Type} [LinearOrder V] [Fintype V]
    (M : AbstractSimplicialComplex V) (q : ℕ) :
    Function.Injective (cocycleSphereChainMapSubtype (G := G) M q) := by
  intro z z' h
  apply Subtype.ext
  apply (cochainEquivNormalizedCochainHom M q).injective
  rw [← cancel_mono (HomologicalComplex.singleObjXSelf
    (ComplexShape.down ℕ) q (AddCommGrpCat.of G)).inv]
  simpa only [cocycleSphereChainMapSubtype,
    cocycleSphereChainMap_f_self] using
      HomologicalComplex.congr_hom h q

theorem cocycleSphereChainMapSubtype_surjective
    {V : Type} [LinearOrder V] [Fintype V]
    (M : AbstractSimplicialComplex V) (q : ℕ) :
    Function.Surjective (cocycleSphereChainMapSubtype (G := G) M q) := by
  intro F
  let e := HomologicalComplex.singleObjXSelf
    (ComplexShape.down ℕ) q (AddCommGrpCat.of G)
  let φ : NormalizedCochainHom (G := G) M q := F.f q ≫ e.hom
  let c : Cochain M q G := (cochainEquivNormalizedCochainHom M q).symm φ
  have hcφ : cochainEquivNormalizedCochainHom M q c = φ := by
    simp [c]
  have htop : F.f (q + 1) = 0 :=
    (HomologicalComplex.isZero_single_obj_X
      (ComplexShape.down ℕ) q (AddCommGrpCat.of G) (q + 1)
        (by omega)).eq_of_tgt _ _
  have hφ :
      ((orderedComplexSSet M).normalizedChainComplex integralCoefficients).d
          (q + 1) q ≫ φ = 0 := by
    dsimp [φ]
    rw [← Category.assoc, ← F.comm (q + 1) q, htop, zero_comp]
    simp
  have hc : coboundary M q c = 0 := by
    apply (cochainEquivNormalizedCochainHom M (q + 1)).injective
    rw [cochainEquivNormalizedCochainHom_coboundary, map_zero]
    rw [hcφ]
    exact hφ
  refine ⟨⟨c, LinearMap.mem_ker.mpr hc⟩, ?_⟩
  apply HomologicalComplex.hom_ext
  intro i
  by_cases hi : i = q
  · subst i
    rw [cocycleSphereChainMapSubtype, cocycleSphereChainMap_f_self, hcφ]
    simp [φ, e, Category.assoc]
  · exact (HomologicalComplex.isZero_single_obj_X
      (ComplexShape.down ℕ) q (AddCommGrpCat.of G) i hi).eq_of_tgt _ _

theorem cocycleSphereChainMapSubtype_bijective
    {V : Type} [LinearOrder V] [Fintype V]
    (M : AbstractSimplicialComplex V) (q : ℕ) :
    Function.Bijective (cocycleSphereChainMapSubtype (G := G) M q) :=
  ⟨cocycleSphereChainMapSubtype_injective M q,
    cocycleSphereChainMapSubtype_surjective M q⟩

def cocycleSphereChainMapSubtypeAddHom
    {V : Type} [LinearOrder V] [Fintype V]
    (M : AbstractSimplicialComplex V) (q : ℕ) :
    LinearMap.ker (coboundary (G := G) M q) →+
      ((orderedComplexSSet M).normalizedChainComplex integralCoefficients ⟶
        StandardModels.sphereComplex (AddCommGrpCat.of G) q) where
  toFun := cocycleSphereChainMapSubtype M q
  map_zero' := by
    apply HomologicalComplex.hom_ext
    intro i
    by_cases hi : i = q
    · subst i
      simp [cocycleSphereChainMapSubtype]
    · exact (HomologicalComplex.isZero_single_obj_X
        (ComplexShape.down ℕ) q (AddCommGrpCat.of G) i hi).eq_of_tgt _ _
  map_add' z z' := by
    apply HomologicalComplex.hom_ext
    intro i
    by_cases hi : i = q
    · subst i
      simp [cocycleSphereChainMapSubtype]
    · exact (HomologicalComplex.isZero_single_obj_X
        (ComplexShape.down ℕ) q (AddCommGrpCat.of G) i hi).eq_of_tgt _ _

/-- Cocyles are exactly the normalized-chain maps into the one-term sphere. -/
def cocycleSphereChainMapSubtypeEquiv
    {V : Type} [LinearOrder V] [Fintype V]
    (M : AbstractSimplicialComplex V) (q : ℕ) :
    LinearMap.ker (coboundary (G := G) M q) ≃+
      ((orderedComplexSSet M).normalizedChainComplex integralCoefficients ⟶
        StandardModels.sphereComplex (AddCommGrpCat.of G) q) :=
  AddEquiv.ofBijective (cocycleSphereChainMapSubtypeAddHom M q)
    (cocycleSphereChainMapSubtype_bijective M q)

/-- Chain maps on `Δⁿ`, after Dold--Kan, are classified by evaluation on the
canonical top simplex. -/
def standardNormalizedChainMapTopEquiv
    (n : ℕ) (C : ChainComplex AddCommGrpCat ℕ) :
    ((orderedComplexSSet (standardSimplex n)).normalizedChainComplex
        integralCoefficients ⟶ C) ≃+
      (CategoryTheory.Abelian.DoldKan.Γ.obj C).obj (op ⦋n⦌) :=
  (denormalizeNormalizedChainMapEquiv
      (orderedComplexSSet (standardSimplex n)) C).trans
    (standardFreeMapTopEquiv n (CategoryTheory.Abelian.DoldKan.Γ.obj C))

/-- Evaluation of the actual global `cochainToLMap` construction on the top
simplex is an additive equivalence. -/
def standardGlobalLEquiv (n q : ℕ) :
    StandardCochain n q G ≃+
      (StandardModels.L (AddCommGrpCat.of G) (q + 1)).obj (op ⦋n⦌) :=
  (cochainDiskChainMapEquiv (standardSimplex n) q).trans
    (standardNormalizedChainMapTopEquiv n
      (StandardModels.diskComplex (AddCommGrpCat.of G) (q + 1)))

@[simp]
theorem standardGlobalLEquiv_apply (n q : ℕ)
    (c : StandardCochain n q G) :
    standardGlobalLEquiv (G := G) n q c =
      (cochainToLMap (standardSimplex n) q c).app
        (op ⦋n⦌) (standardSimplexTop n) := by
  rfl

/-- Evaluation of the actual global `cocycleToKMap` construction on the top
simplex is an additive equivalence. -/
def standardGlobalKEquiv (n q : ℕ) :
    StandardCocycle n q G ≃+
      (StandardModels.K (AddCommGrpCat.of G) q).obj (op ⦋n⦌) :=
  (cocycleSphereChainMapSubtypeEquiv (standardSimplex n) q).trans
    (standardNormalizedChainMapTopEquiv n
      (StandardModels.sphereComplex (AddCommGrpCat.of G) q))

@[simp]
theorem standardGlobalKEquiv_apply (n q : ℕ)
    (z : StandardCocycle n q G) :
    standardGlobalKEquiv (G := G) n q z =
      (cocycleToKMap (standardSimplex n) q z.1
        (LinearMap.mem_ker.mp z.2)).app
          (op ⦋n⦌) (standardSimplexTop n) := by
  rfl

/-- Additive-map wrapper for global `L` evaluation. -/
def standardGlobalLValue (n q : ℕ) :
    StandardCochain n q G →+
      (StandardModels.L (AddCommGrpCat.of G) (q + 1)).obj (op ⦋n⦌) :=
  (standardGlobalLEquiv (G := G) n q).toAddMonoidHom

/-- Additive-map wrapper for global `K` evaluation. -/
def standardGlobalKValue (n q : ℕ) :
    StandardCocycle n q G →+
      (StandardModels.K (AddCommGrpCat.of G) q).obj (op ⦋n⦌) :=
  (standardGlobalKEquiv (G := G) n q).toAddMonoidHom

@[simp]
theorem standardGlobalLValue_apply (n q : ℕ)
    (c : StandardCochain n q G) :
    standardGlobalLValue (G := G) n q c =
      (cochainToLMap (standardSimplex n) q c).app
        (op ⦋n⦌) (standardSimplexTop n) :=
  standardGlobalLEquiv_apply n q c

@[simp]
theorem standardGlobalKValue_apply (n q : ℕ)
    (z : StandardCocycle n q G) :
    standardGlobalKValue (G := G) n q z =
      (cocycleToKMap (standardSimplex n) q z.1
        (LinearMap.mem_ker.mp z.2)).app
          (op ⦋n⦌) (standardSimplexTop n) :=
  standardGlobalKEquiv_apply n q z

/-- The actual automorphism converting the explicit `L` coordinate
classification into evaluation of the global Dold--Kan construction. -/
def standardLConstructionComparison (n q : ℕ) :
    (StandardModels.L (AddCommGrpCat.of G) (q + 1)).obj (op ⦋n⦌) ≃+
      (StandardModels.L (AddCommGrpCat.of G) (q + 1)).obj (op ⦋n⦌) :=
  (standardCochainEquivLLevel n q G).symm.trans
    (standardGlobalLEquiv n q)

@[simp]
theorem standardLConstructionComparison_apply (n q : ℕ)
    (c : StandardCochain n q G) :
    standardLConstructionComparison (G := G) n q
        (standardCochainEquivLLevel n q G c) =
      (cochainToLMap (standardSimplex n) q c).app
        (op ⦋n⦌) (standardSimplexTop n) := by
  rw [standardLConstructionComparison]
  simp only [AddEquiv.trans_apply, AddEquiv.symm_apply_apply]
  exact standardGlobalLEquiv_apply n q c

/-- The actual automorphism converting the explicit `K` coordinate
classification into evaluation of the global Dold--Kan construction. -/
def standardKConstructionComparison (n q : ℕ) :
    (StandardModels.K (AddCommGrpCat.of G) q).obj (op ⦋n⦌) ≃+
      (StandardModels.K (AddCommGrpCat.of G) q).obj (op ⦋n⦌) :=
  (standardCocycleEquivKLevel n q G).symm.trans
    (standardGlobalKEquiv n q)

@[simp]
theorem standardKConstructionComparison_apply (n q : ℕ)
    (z : StandardCocycle n q G) :
    standardKConstructionComparison (G := G) n q
        (standardCocycleEquivKLevel n q G z) =
      (cocycleToKMap (standardSimplex n) q z.1
        (LinearMap.mem_ker.mp z.2)).app
          (op ⦋n⦌) (standardSimplexTop n) := by
  rw [standardKConstructionComparison]
  simp only [AddEquiv.trans_apply, AddEquiv.symm_apply_apply]
  exact standardGlobalKEquiv_apply n q z

/-- Evaluation of the global construction commutes strictly with the genuine
simplicial map `d`; no coordinate comparison is used here. -/
theorem standardGlobal_d_eq_coboundary (n q : ℕ)
    (c : StandardCochain n q G) :
    (StandardModels.d (AddCommGrpCat.of G) (q + 1)).app (op ⦋n⦌)
        (standardGlobalLValue (G := G) n q c) =
      standardGlobalKValue (G := G) n (q + 1)
        (standardCoboundaryCocycle n q G c) := by
  change ((cochainToLMap (standardSimplex n) q c ≫
      Functor.whiskerRight
        (StandardModels.d (AddCommGrpCat.of G) (q + 1))
        (forget AddCommGrpCat)).app (op ⦋n⦌)) (standardSimplexTop n) =
    (cocycleToKMap (standardSimplex n) (q + 1)
      (coboundary (standardSimplex n) q c)
      (coboundary_coboundary (standardSimplex n) q c)).app
        (op ⦋n⦌) (standardSimplexTop n)
  rw [cochainToLMap_comp_d]

/-- The `L` and `K` comparison automorphisms commute with the actual map `d`.
This is the model-independent replacement for a pointwise definitional
equality between two implementations of Dold--Kan. -/
theorem standardConstructionComparisons_d (n q : ℕ)
    (x : (StandardModels.L (AddCommGrpCat.of G) (q + 1)).obj (op ⦋n⦌)) :
    (StandardModels.d (AddCommGrpCat.of G) (q + 1)).app (op ⦋n⦌)
        (standardLConstructionComparison (G := G) n q x) =
      standardKConstructionComparison (G := G) n (q + 1)
        ((StandardModels.d (AddCommGrpCat.of G) (q + 1)).app
          (op ⦋n⦌) x) := by
  obtain ⟨c, rfl⟩ := (standardCochainEquivLLevel n q G).surjective x
  rw [standardLConstructionComparison_apply]
  rw [standardClassifications_d_eq_coboundary]
  rw [standardKConstructionComparison_apply]
  change ((cochainToLMap (standardSimplex n) q c ≫
      Functor.whiskerRight
        (StandardModels.d (AddCommGrpCat.of G) (q + 1))
        (forget AddCommGrpCat)).app (op ⦋n⦌)) (standardSimplexTop n) =
    (cocycleToKMap (standardSimplex n) (q + 1)
      (coboundary (standardSimplex n) q c)
      (coboundary_coboundary (standardSimplex n) q c)).app
        (op ⦋n⦌) (standardSimplexTop n)
  rw [cochainToLMap_comp_d]

end SimplicialCochain

end GeneralSphereT
