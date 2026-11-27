import Formalization.OpenDisk.PhaseDualityNormalizedMaps
import Mathlib.AlgebraicTopology.SimplicialObject.ChainHomotopy
import Mathlib.AlgebraicTopology.SimplicialSet.Homotopy
import Mathlib.AlgebraicTopology.DoldKan.HomotopyEquivalence

set_option linter.style.header false
set_option backward.isDefEq.respectTransparency false

/-!
# Native simplicial homotopy gives actual normalized-chain homotopy

The free simplicial abelian universal property extends a cylinder homotopy
linearly.  Passing from alternating chains to normalized Moore chains uses
the actual split inclusion and projection.  The result concerns the
concrete normalized source and target complexes, not a relabeled quotient.
-/

noncomputable section

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits Opposite Simplicial
open GeneralSphereT.SimplicialCochain GeneralSphereT.Section4
open GeneralSphereT.Section4.UnderlyingSSet

namespace OpenDisk.NormalizedMaps

universe u

abbrev freeMap {X Y : SSet.{u}} (f : X ⟶ Y) :
    freeSimplicialAbelian X ⟶ freeSimplicialAbelian Y :=
  ((SimplicialObject.whiskering _ _).obj (sigmaConst.obj integralCoefficients)).map f

theorem generator_naturality {X Y : SSet.{u}} (f : X ⟶ Y) :
    f ≫ freeSimplicialAbelianGenerator Y = freeSimplicialAbelianGenerator X ≫
      Functor.whiskerRight (freeMap f) (forget AddCommGrpCat) := by
  ext Δ x
  exact (ConcreteCategory.congr_hom
    (Sigma.ι_comp_map'
      (f := fun _ : X.obj Δ => integralCoefficients)
      (g := fun _ : Y.obj Δ => integralCoefficients)
      (fun y : X.obj Δ => f.app Δ y)
      (fun _ => 𝟙 integralCoefficients) x) (ULift.up (1 : ℤ))).symm

theorem freeLift_eq_map_counit (X : SSet.{u}) (A : SimplicialObject AddCommGrpCat.{u})
    (f : X ⟶ underlyingSSet A) :
    freeLift X A f = freeMap f ≫ freeLift (underlyingSSet A) A (𝟙 _) := by
  apply (freeMapEquiv X A).injective
  change freeSimplicialAbelianGenerator X ≫
      Functor.whiskerRight (freeLift X A f) (forget AddCommGrpCat) =
    freeSimplicialAbelianGenerator X ≫
      Functor.whiskerRight (freeMap f ≫ freeLift (underlyingSSet A) A (𝟙 _))
        (forget AddCommGrpCat)
  rw [freeLift_generator, Functor.whiskerRight_comp, ← Category.assoc,
    ← generator_naturality, Category.assoc, freeLift_generator, Category.comp_id]

/-- Linear extension of an actual simplicial-set cylinder homotopy. -/
def freeLiftHomotopy {X : SSet.{u}} {A : SimplicialObject AddCommGrpCat.{u}}
    {f g : X ⟶ underlyingSSet A} (H : SSet.Homotopy f g) :
    SimplicialObject.Homotopy (freeLift X A f) (freeLift X A g) := by
  have h := (H.toSimplicialObjectHomotopy.whiskerRight
    (sigmaConst.obj integralCoefficients)).postcomp
      (freeLift (underlyingSSet A) A (𝟙 _))
  change SimplicialObject.Homotopy
    (freeMap f ≫ freeLift (underlyingSSet A) A (𝟙 _))
    (freeMap g ≫ freeLift (underlyingSSet A) A (𝟙 _)) at h
  simpa only [← freeLift_eq_map_counit] using h

open AlgebraicTopology AlgebraicTopology.DoldKan

/-- The actual normalized Moore functor preserves combinatorial homotopies. -/
def normalizedMooreHomotopy
    {A B : SimplicialObject AddCommGrpCat.{u}} {f g : A ⟶ B}
    (H : SimplicialObject.Homotopy f g) :
    Homotopy (CategoryTheory.Abelian.DoldKan.N.map f)
      (CategoryTheory.Abelian.DoldKan.N.map g) := by
  letI : Preadditive AddCommGrpCat.{u} := AddCommGrpCat.instAbelian.toPreadditive
  have h := (H.toChainHomotopy.compLeft (inclusionOfMooreComplexMap A)).compRight
    (PInftyToNormalizedMooreComplex B)
  have hid : inclusionOfMooreComplexMap A ≫ PInftyToNormalizedMooreComplex A = 𝟙 _ :=
    (splitMonoInclusionOfMooreComplexMap A).id
  have heq (k : A ⟶ B) :
      inclusionOfMooreComplexMap A ≫ AlternatingFaceMapComplex.map k ≫
          PInftyToNormalizedMooreComplex B = NormalizedMooreComplex.map k := by
    rw [PInftyToNormalizedMooreComplex_naturality, ← Category.assoc, hid, Category.id_comp]
  change Homotopy (NormalizedMooreComplex.map f) (NormalizedMooreComplex.map g)
  refine (Homotopy.ofEq ?_).trans (h.trans (Homotopy.ofEq ?_))
  · exact ((Category.assoc _ _ _).trans (heq f)).symm
  · exact (Category.assoc _ _ _).trans (heq g)

/-- The concrete normalized-chain map represented by an actual simplicial map. -/
def normalizedChainMapOfSimplicialMap (X : SSet.{u}) (A : SimplicialObject AddCommGrpCat.{u})
    (f : X ⟶ underlyingSSet A) :
    X.normalizedChainComplex integralCoefficients ⟶ CategoryTheory.Abelian.DoldKan.N.obj A :=
  (normalizedChainIsoDoldKanN X).hom ≫ CategoryTheory.Abelian.DoldKan.N.map (freeLift X A f)

/-- Native simplicial homotopy gives an actual homotopy of the normalized chain maps. -/
def nativeNormalizedChainHomotopy {X : SSet.{u}} {A : SimplicialObject AddCommGrpCat.{u}}
    {f g : X ⟶ underlyingSSet A} (H : SSet.Homotopy f g) :
    Homotopy (normalizedChainMapOfSimplicialMap X A f)
      (normalizedChainMapOfSimplicialMap X A g) :=
  (normalizedMooreHomotopy (freeLiftHomotopy H)).compLeft (normalizedChainIsoDoldKanN X).hom

end OpenDisk.NormalizedMaps
