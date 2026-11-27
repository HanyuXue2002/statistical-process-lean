import Formalization.Section4GlobalRelationPathLocalZero
import Formalization.Section4StandardSimplexConstructionCompatibility
import Formalization.Section4StrictFSectionsNativeKernel

set_option linter.style.header false
set_option backward.isDefEq.respectTransparency false

/-!
# Local cochains classify simplices of the Dold--Kan disk

For a nondegenerate simplex `x`, evaluation on `x` identifies cochains on its
support with the corresponding level of `L(G,q+1)`.  This is the local
bijection needed before applying the integral cube-gluing lemma.
-/

noncomputable section

open CategoryTheory Opposite Simplicial

namespace GeneralSphereT.SimplicialCochain

open GeneralSphereT.PathAlgebra
open GeneralSphereT.StandardModels

universe u

variable {V G : Type u} [LinearOrder V] [Fintype V] [AddCommGroup G]

/-- Turning an ambient local face into a support face and back is the
identity. -/
@[simp]
theorem faceInToSupportSimplex_supportMap
    (M : AbstractSimplicialComplex V) {n : ℕ}
    (x : (orderedComplexSSet M).nonDegenerate n) (r : ℕ)
    (τ : Simplex (nonDegenerateSimplexSupportComplex M x) r) :
    faceInToSupportSimplex M x r
        ⟨(nonDegenerateSimplexSupportMap M x).mapSimplex τ, by
          intro v hv
          rcases Finset.mem_map.mp hv with ⟨i, hi, rfl⟩
          exact i.2⟩ = τ := by
  apply Subtype.ext
  ext v
  simp only [faceInToSupportSimplex,
    OrderedSimplicialMap.mapSimplex_val, Finset.mem_map,
    RelEmbedding.coe_toEmbedding, nonDegenerateSimplexSupportMap_apply,
    Finset.mem_attach, true_and, Subtype.exists]
  aesop

/-- The elementary local-coordinate identification is onto. -/
theorem localCochainToStandard_surjective
    (M : AbstractSimplicialComplex V) {n : ℕ}
    (x : (orderedComplexSSet M).nonDegenerate n) (r : ℕ) :
    Function.Surjective (localCochainToStandard (G := G) M x r) := by
  intro c
  let a : Configuration
      (facesIn M r (nonDegenerateSimplexFacet M x)) G :=
    Finsupp.equivFunOnFinite.symm fun τ =>
      c (faceInToSupportSimplex M x r τ)
  refine ⟨a, ?_⟩
  ext τ
  change c (faceInToSupportSimplex M x r
      ⟨(nonDegenerateSimplexSupportMap M x).mapSimplex τ, _⟩) = c τ
  rw [faceInToSupportSimplex_supportMap]

/-- Additive form of the local-coordinate identification. -/
def localCochainToStandardHom
    (M : AbstractSimplicialComplex V) {n : ℕ}
    (x : (orderedComplexSSet M).nonDegenerate n) (r : ℕ) :
    Configuration (facesIn M r (nonDegenerateSimplexFacet M x)) G →+
      Cochain (nonDegenerateSimplexSupportComplex M x) r G where
  toFun := localCochainToStandard M x r
  map_zero' := by ext τ; rfl
  map_add' a b := by ext τ; rfl

/-- Local configurations and cochains on the full support simplex are
additively equivalent. -/
def localCochainToStandardEquiv
    (M : AbstractSimplicialComplex V) {n : ℕ}
    (x : (orderedComplexSSet M).nonDegenerate n) (r : ℕ) :
    Configuration (facesIn M r (nonDegenerateSimplexFacet M x)) G ≃+
      Cochain (nonDegenerateSimplexSupportComplex M x) r G :=
  AddEquiv.ofBijective (localCochainToStandardHom M x r)
    ⟨localCochainToStandard_injective M x r,
      localCochainToStandard_surjective M x r⟩

/-- Prescribe the value of a map out of the free simplicial abelian group on
a full support simplex at its top generator. -/
def supportSimplexFreeLift
    (M : AbstractSimplicialComplex V) {n : ℕ}
    (x : (orderedComplexSSet M).nonDegenerate n)
    (A : SimplicialObject AddCommGrpCat.{u})
    (y : A.obj (Opposite.op (SimplexCategory.mk n))) :
    freeSimplicialAbelian
      (orderedComplexSSet (nonDegenerateSimplexSupportComplex M x)) ⟶ A where
  app Δ := CategoryTheory.Limits.Sigma.desc fun z =>
    integerGeneratorHom (A.map (nonDegenerateSimplexSupportHom M x z).op y)
  naturality Δ Δ' θ := by
    apply CategoryTheory.Limits.Sigma.hom_ext
    intro z
    apply integralCoefficients_hom_ext
    simp only [ConcreteCategory.comp_apply]
    have hg :
        (freeSimplicialAbelian
          (orderedComplexSSet
            (nonDegenerateSimplexSupportComplex M x))).map θ
          ((CategoryTheory.Limits.Sigma.ι (fun _ :
              (orderedComplexSSet
                (nonDegenerateSimplexSupportComplex M x)).obj Δ =>
                integralCoefficients) z) (ULift.up (1 : ℤ))) =
        (CategoryTheory.Limits.Sigma.ι (fun _ :
            (orderedComplexSSet
              (nonDegenerateSimplexSupportComplex M x)).obj Δ' =>
              integralCoefficients)
          ((orderedComplexSSet
            (nonDegenerateSimplexSupportComplex M x)).map θ z))
              (ULift.up (1 : ℤ)) := by
      symm
      exact ConcreteCategory.congr_hom
        ((freeSimplicialAbelianGenerator
          (orderedComplexSSet
            (nonDegenerateSimplexSupportComplex M x))).naturality θ) z
    have hdesc' :
        (CategoryTheory.Limits.Sigma.desc fun z' :
          (orderedComplexSSet
            (nonDegenerateSimplexSupportComplex M x)).obj Δ' =>
            integerGeneratorHom
              (A.map (nonDegenerateSimplexSupportHom M x z').op y))
          ((CategoryTheory.Limits.Sigma.ι (fun _ :
              (orderedComplexSSet
                (nonDegenerateSimplexSupportComplex M x)).obj Δ' =>
                integralCoefficients)
            ((orderedComplexSSet
              (nonDegenerateSimplexSupportComplex M x)).map θ z))
                (ULift.up (1 : ℤ))) =
          A.map (nonDegenerateSimplexSupportHom M x
            ((orderedComplexSSet
              (nonDegenerateSimplexSupportComplex M x)).map θ z)).op y := by
      exact (CategoryTheory.congr_fun
        (CategoryTheory.Limits.Sigma.ι_desc
          (fun z' : (orderedComplexSSet
            (nonDegenerateSimplexSupportComplex M x)).obj Δ' =>
              integerGeneratorHom
                (A.map (nonDegenerateSimplexSupportHom M x z').op y))
          ((orderedComplexSSet
            (nonDegenerateSimplexSupportComplex M x)).map θ z))
        (ULift.up (1 : ℤ))).trans (integerGeneratorHom_one _)
    have hdesc :
        (CategoryTheory.Limits.Sigma.desc fun z' :
          (orderedComplexSSet
            (nonDegenerateSimplexSupportComplex M x)).obj Δ =>
            integerGeneratorHom
              (A.map (nonDegenerateSimplexSupportHom M x z').op y))
          ((CategoryTheory.Limits.Sigma.ι (fun _ :
              (orderedComplexSSet
                (nonDegenerateSimplexSupportComplex M x)).obj Δ =>
                integralCoefficients) z) (ULift.up (1 : ℤ))) =
          A.map (nonDegenerateSimplexSupportHom M x z).op y := by
      exact (CategoryTheory.congr_fun
        (CategoryTheory.Limits.Sigma.ι_desc
          (fun z' : (orderedComplexSSet
            (nonDegenerateSimplexSupportComplex M x)).obj Δ =>
              integerGeneratorHom
                (A.map (nonDegenerateSimplexSupportHom M x z').op y)) z)
        (ULift.up (1 : ℤ))).trans (integerGeneratorHom_one _)
    calc
      _ = (CategoryTheory.Limits.Sigma.desc fun z' :
          (orderedComplexSSet
            (nonDegenerateSimplexSupportComplex M x)).obj Δ' =>
            integerGeneratorHom
              (A.map (nonDegenerateSimplexSupportHom M x z').op y))
          ((CategoryTheory.Limits.Sigma.ι (fun _ :
              (orderedComplexSSet
                (nonDegenerateSimplexSupportComplex M x)).obj Δ' =>
                integralCoefficients)
            ((orderedComplexSSet
              (nonDegenerateSimplexSupportComplex M x)).map θ z))
                (ULift.up (1 : ℤ))) := congrArg _ hg
      _ = A.map (nonDegenerateSimplexSupportHom M x
            ((orderedComplexSSet
              (nonDegenerateSimplexSupportComplex M x)).map θ z)).op y :=
        hdesc'
      _ = A.map θ
          (A.map (nonDegenerateSimplexSupportHom M x z).op y) := by
        rw [← ConcreteCategory.comp_apply, ← A.map_comp]
        rfl
      _ = _ := congrArg (fun t => A.map θ t) hdesc.symm

@[simp]
theorem supportSimplexFreeLift_eval_top
    (M : AbstractSimplicialComplex V) {n : ℕ}
    (x : (orderedComplexSSet M).nonDegenerate n)
    (A : SimplicialObject AddCommGrpCat.{u})
    (y : A.obj (Opposite.op (SimplexCategory.mk n))) :
    (supportSimplexFreeLift M x A y).app
        (Opposite.op (SimplexCategory.mk n))
          (nonDegenerateSimplexSupportTopGenerator M x) = y := by
  have hid : nonDegenerateSimplexSupportHom M x
      (nonDegenerateSimplexSupportTop M x) =
        𝟙 (SimplexCategory.mk n) := by
    apply SimplexCategory.Hom.ext
    apply OrderHom.ext
    funext i
    change (nonDegenerateSimplexSupportOrderIso M x).symm
      ((nonDegenerateSimplexSupportTop M x).1 i) = i
    have htop : (nonDegenerateSimplexSupportTop M x).1 i =
        nonDegenerateSimplexSupportOrderIso M x i := by
      exact (nonDegenerateSimplexSupportOrderIso_apply M x i).symm
    rw [htop]
    exact (nonDegenerateSimplexSupportOrderIso M x).symm_apply_apply i
  change
    (CategoryTheory.Limits.Sigma.desc fun z :
      (orderedComplexSSet
        (nonDegenerateSimplexSupportComplex M x)).obj
          (Opposite.op (SimplexCategory.mk n)) =>
        integerGeneratorHom
          (A.map (nonDegenerateSimplexSupportHom M x z).op y))
      ((CategoryTheory.Limits.Sigma.ι (fun _ :
          (orderedComplexSSet
            (nonDegenerateSimplexSupportComplex M x)).obj
              (Opposite.op (SimplexCategory.mk n)) => integralCoefficients)
        (nonDegenerateSimplexSupportTop M x)) (ULift.up (1 : ℤ))) = y
  calc
    _ = integerGeneratorHom
        (A.map (nonDegenerateSimplexSupportHom M x
          (nonDegenerateSimplexSupportTop M x)).op y)
          (ULift.up (1 : ℤ)) :=
      CategoryTheory.congr_fun
        (CategoryTheory.Limits.Sigma.ι_desc
          (fun z : (orderedComplexSSet
            (nonDegenerateSimplexSupportComplex M x)).obj
              (Opposite.op (SimplexCategory.mk n)) =>
            integerGeneratorHom
              (A.map (nonDegenerateSimplexSupportHom M x z).op y))
          (nonDegenerateSimplexSupportTop M x)) (ULift.up (1 : ℤ))
    _ = A.map (nonDegenerateSimplexSupportHom M x
        (nonDegenerateSimplexSupportTop M x)).op y :=
      integerGeneratorHom_one _
    _ = y := by rw [hid]; simp

/-- The two-term disk chain map is classified by its bottom cochain in any
universe. -/
theorem cochainDiskChainMap_surjective_universe
    (N : AbstractSimplicialComplex V) (q : ℕ) :
    Function.Surjective (cochainDiskChainMap (G := G) N q) := by
  intro F
  let e₀ := HomologicalComplex.doubleXIso₀ (𝟙 (AddCommGrpCat.of G))
    (ComplexShape.down_mk (q + 1) q rfl)
  let e₁ := HomologicalComplex.doubleXIso₁ (𝟙 (AddCommGrpCat.of G))
    (ComplexShape.down_mk (q + 1) q rfl) (by omega)
  let φ : NormalizedCochainHom (G := G) N q := F.f q ≫ e₁.hom
  let c : Cochain N q G := (cochainEquivNormalizedCochainHom N q).symm φ
  refine ⟨c, ?_⟩
  apply HomologicalComplex.to_double_hom_ext
  · rw [cochainDiskChainMap_f_top]
    rw [cochainEquivNormalizedCochainHom_coboundary]
    have hc : cochainEquivNormalizedCochainHom N q c = F.f q ≫ e₁.hom := by
      simp [c, φ]
    rw [hc, ← CategoryTheory.Category.assoc]
    rw [← F.comm (q + 1) q]
    rw [HomologicalComplex.double_d]
    · simp [e₁, CategoryTheory.Category.assoc]
    · omega
  · rw [cochainDiskChainMap_f_bottom]
    have hc : cochainEquivNormalizedCochainHom N q c = F.f q ≫ e₁.hom := by
      simp [c, φ]
    rw [hc]
    simp [e₁, CategoryTheory.Category.assoc]

/-- Evaluation at the top of a full support simplex is surjective. -/
theorem supportCochainLValue_surjective
    (M : AbstractSimplicialComplex V) (q : ℕ) {n : ℕ}
    (x : (orderedComplexSSet M).nonDegenerate n) :
    Function.Surjective (fun c :
        Cochain (nonDegenerateSimplexSupportComplex M x) q G =>
      cochainLValue (nonDegenerateSimplexSupportComplex M x) q
        (Opposite.op (SimplexCategory.mk n))
        (nonDegenerateSimplexSupportTop M x) c) := by
  intro y
  let X := orderedComplexSSet (nonDegenerateSimplexSupportComplex M x)
  let C := StandardModels.diskComplex (AddCommGrpCat.of G) (q + 1)
  let Φ : freeSimplicialAbelian X ⟶
      CategoryTheory.Abelian.DoldKan.Γ.obj C :=
    supportSimplexFreeLift M x _ y
  obtain ⟨F, hF⟩ :=
    (denormalizeNormalizedChainMap_bijective X C).2 Φ
  obtain ⟨c, hc⟩ :=
    cochainDiskChainMap_surjective_universe
      (G := G) (nonDegenerateSimplexSupportComplex M x) q F
  refine ⟨c, ?_⟩
  change
    (denormalizeNormalizedChainMap X
      (cochainDiskChainMap
        (nonDegenerateSimplexSupportComplex M x) q c)).app
          (Opposite.op (SimplexCategory.mk n))
            (nonDegenerateSimplexSupportTopGenerator M x) = y
  rw [hc, hF]
  exact supportSimplexFreeLift_eval_top M x _ y

/-- Local evaluation is surjective. -/
theorem localCochainLValue_surjective
    (M : AbstractSimplicialComplex V) (q n : ℕ)
    (x : (orderedComplexSSet M).nonDegenerate n) :
    Function.Surjective (localCochainLValue (G := G) M q n x) := by
  intro y
  obtain ⟨c, hc⟩ := supportCochainLValue_surjective M q x y
  obtain ⟨a, rfl⟩ := localCochainToStandard_surjective M x q c
  exact ⟨a, hc⟩

set_option maxHeartbeats 800000 in
-- Unfolding both support-simplex evaluations is elaboration-heavy.
/-- The additive local evaluation used for distributions agrees with the
support-simplex evaluation. -/
theorem localCochainLValueHom_eq
    (M : AbstractSimplicialComplex V) (q n : ℕ)
    (x : (orderedComplexSSet M).nonDegenerate n)
    (a : Configuration
      (facesIn M q (nonDegenerateSimplexFacet M x)) G) :
    localCochainLValueHom M q n x a =
      localCochainLValue M q n x a := by
  let c : Cochain M q G := coordinateExtension
    (facesIn M q (nonDegenerateSimplexFacet M x)) a
  have h := localCochainLValue_restrict M q n x c
  have hres : restrictCochain M q (nonDegenerateSimplexFacet M x) c = a := by
    exact coordinateRestriction_coordinateExtension
      (facesIn M q (nonDegenerateSimplexFacet M x)) a
  rw [hres] at h
  change cochainLValue M q _ x.1 c = localCochainLValue M q n x a
  exact h.symm

/-- Local cochains on a nondegenerate simplex are additively equivalent to
the corresponding `L`-simplices. -/
def localCochainLValueEquiv
    (M : AbstractSimplicialComplex V) (q n : ℕ)
    (x : (orderedComplexSSet M).nonDegenerate n) :
    Configuration (facesIn M q (nonDegenerateSimplexFacet M x)) G ≃+
      (L (AddCommGrpCat.of G) (q + 1)).obj
        (Opposite.op (SimplexCategory.mk n)) :=
  AddEquiv.ofBijective (localCochainLValueHom M q n x)
    ⟨by
        intro a b h
        apply localCochainLValue_injective M q n x
        simpa only [localCochainLValueHom_eq] using h,
      by
        intro y
        obtain ⟨a, ha⟩ := localCochainLValue_surjective M q n x y
        exact ⟨a, by simpa only [localCochainLValueHom_eq] using ha⟩⟩

@[simp]
theorem localCochainLValueEquiv_apply
    (M : AbstractSimplicialComplex V) (q n : ℕ)
    (x : (orderedComplexSSet M).nonDegenerate n)
    (a : Configuration
      (facesIn M q (nonDegenerateSimplexFacet M x)) G) :
    localCochainLValueEquiv M q n x a =
      localCochainLValueHom M q n x a :=
  rfl

end GeneralSphereT.SimplicialCochain
