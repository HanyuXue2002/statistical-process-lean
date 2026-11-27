import Formalization.Section4StandardSimplexConstructionCompatibility

set_option linter.style.header false
set_option backward.isDefEq.respectTransparency false

/-!
# The actual normalized-chain / simplicial-map correspondence

The free simplicial abelian universal property is proved for every simplicial
set, not only for standard simplices.  Composing it with the existing
Dold--Kan equivalence gives a genuine additive bijection between normalized
chain maps and simplicial maps into the denormalized target.

This is the raw-map bridge; preservation and reflection of relative
homotopy are separate mathematical assertions.
-/

noncomputable section

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits Opposite Simplicial
open GeneralSphereT.SimplicialCochain GeneralSphereT.Section4
open GeneralSphereT.Section4.UnderlyingSSet

namespace OpenDisk.NormalizedMaps

universe u
variable (X : SSet.{u}) (A : SimplicialObject AddCommGrpCat.{u})

/-- Extend a simplicial-set map linearly on the actual simplex generators. -/
def freeLift (f : X ⟶ underlyingSSet A) : freeSimplicialAbelian X ⟶ A where
  app Δ := Sigma.desc (fun x : X.obj Δ => integerGeneratorHom (f.app Δ x))
  naturality Δ Δ' θ := by
    apply Sigma.hom_ext
    intro x
    apply integralCoefficients_hom_ext
    simp only [ConcreteCategory.comp_apply]
    have hg := ConcreteCategory.congr_hom ((freeSimplicialAbelianGenerator X).naturality θ) x
    change (Sigma.ι (fun _ : X.obj Δ' => integralCoefficients) (X.map θ x))
        (ULift.up (1 : ℤ)) =
      (freeSimplicialAbelian X).map θ
        ((Sigma.ι (fun _ : X.obj Δ => integralCoefficients) x) (ULift.up (1 : ℤ))) at hg
    have hdesc (Δ : SimplexCategoryᵒᵖ) (z : X.obj Δ) :
        (Sigma.desc (fun y : X.obj Δ => integerGeneratorHom (f.app Δ y)))
          ((Sigma.ι (fun _ : X.obj Δ => integralCoefficients) z)
            (ULift.up (1 : ℤ))) = f.app Δ z := by
      exact (ConcreteCategory.congr_hom (Sigma.ι_desc
        (fun y : X.obj Δ => integerGeneratorHom (f.app Δ y)) z)
        (ULift.up (1 : ℤ))).trans (integerGeneratorHom_one _)
    calc
      _ = (Sigma.desc (fun y : X.obj Δ' => integerGeneratorHom (f.app Δ' y)))
          ((Sigma.ι (fun _ : X.obj Δ' => integralCoefficients) (X.map θ x))
            (ULift.up (1 : ℤ))) :=
        congrArg (Sigma.desc (fun y : X.obj Δ' => integerGeneratorHom (f.app Δ' y))) hg.symm
      _ = f.app Δ' (X.map θ x) := hdesc Δ' (X.map θ x)
      _ = A.map θ (f.app Δ x) := f.naturality_apply θ x
      _ = _ := congrArg (A.map θ) (hdesc Δ x).symm

@[simp]
theorem freeLift_generator (f : X ⟶ underlyingSSet A) :
    freeSimplicialAbelianGenerator X ≫
      Functor.whiskerRight (freeLift X A f) (forget AddCommGrpCat) = f := by
  ext Δ x
  exact (ConcreteCategory.congr_hom (Sigma.ι_desc
    (fun y : X.obj Δ => integerGeneratorHom (f.app Δ y)) x)
    (ULift.up (1 : ℤ))).trans (integerGeneratorHom_one _)

/-- Maps out of the free simplicial abelian group are determined by generators. -/
theorem freeMap_ext (f g : freeSimplicialAbelian X ⟶ A)
    (h : freeSimplicialAbelianGenerator X ≫
        Functor.whiskerRight f (forget AddCommGrpCat) =
      freeSimplicialAbelianGenerator X ≫
        Functor.whiskerRight g (forget AddCommGrpCat)) : f = g := by
  apply NatTrans.ext
  funext Δ
  apply Sigma.hom_ext
  intro x
  apply integralCoefficients_hom_ext
  exact ConcreteCategory.congr_hom (NatTrans.congr_app h Δ) x

/-- The degreewise free abelian universal property, with its actual generator map. -/
def freeMapEquiv : (freeSimplicialAbelian X ⟶ A) ≃+ (X ⟶ underlyingSSet A) where
  toFun f := freeSimplicialAbelianGenerator X ≫
    Functor.whiskerRight f (forget AddCommGrpCat)
  invFun := freeLift X A
  left_inv f := freeMap_ext X A _ _ (freeLift_generator X A _)
  right_inv := freeLift_generator X A
  map_add' f g := by
    ext Δ x
    rfl

variable (C : ChainComplex AddCommGrpCat.{u} ℕ)

/-- Actual normalized-chain maps correspond bijectively to actual simplicial
maps into the Dold--Kan denormalized target. -/
def normalizedChainMapEquiv :
    (X.normalizedChainComplex integralCoefficients ⟶ C) ≃+
      (X ⟶ underlyingSSet (CategoryTheory.Abelian.DoldKan.Γ.obj C)) :=
  (denormalizeNormalizedChainMapEquiv X C).trans
    (freeMapEquiv X (CategoryTheory.Abelian.DoldKan.Γ.obj C))

@[simp]
theorem normalizedChainMapEquiv_apply
    (f : X.normalizedChainComplex integralCoefficients ⟶ C) :
    normalizedChainMapEquiv X C f = simplicialMapOfNormalizedChainMap X f := rfl

theorem simplicialMapOfNormalizedChainMap_bijective :
    Function.Bijective (simplicialMapOfNormalizedChainMap (C := C) X) :=
  (normalizedChainMapEquiv X C).bijective

end OpenDisk.NormalizedMaps
