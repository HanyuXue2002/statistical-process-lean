import Formalization.Transport.RelativeChainHomotopy
import Formalization.Transport.FundamentalEvaluation

/-! Evaluation of actual simplicial homotopy classes of pairs. The only
homology hypothesis is on the relative fundamental cycle of the source. -/
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
noncomputable section
open CategoryTheory Opposite Simplicial AlgebraicTopology AlgebraicTopology.DoldKan
open GeneralSphereT.Section4.NativeRelativeHomotopyGroup OpenDisk
namespace GeneralSphereT.Transport.RelativeChains

/-- Integral modules with their usual underlying additive group. -/
def integralModules : AddCommGrpCat.{0} ⥤ ModuleCat ℤ where
  obj A := ModuleCat.of ℤ A
  map f := ModuleCat.ofHom f.hom.toIntLinearMap

instance : integralModules.Additive where
  map_add := by intros; rfl
instance : integralModules.Faithful where
  map_injective h := by
    apply AddCommGrpCat.ext
    exact fun x => ConcreteCategory.congr_hom h x
instance : integralModules.Full where
  map_surjective f := ⟨AddCommGrpCat.ofHom f.hom.toAddMonoidHom,by ext x; rfl⟩

local instance : Moore.{0}.Additive := CategoryTheory.Functor.additive_of_preserves_binary_products Moore

abbrev integralChains := Moore.{0} ⋙ integralModules.mapHomologicalComplex (.down ℕ)

variable {X : SSet.{0}} (P : X.Subcomplex) (A : SimplicialObject AddCommGrpCat.{0})
abbrev source := integralChains.obj (relFree P)
abbrev target := integralChains.obj A

instance source_projective (n : ℕ) : Projective ((source P).X n) := by
  let i := (inclusionOfMooreComplexMap (relFree P)).f n
  let p := (PInftyToNormalizedMooreComplex (relFree P)).f n
  have h : i ≫ p = 𝟙 _ := HomologicalComplex.congr_hom (splitMonoInclusionOfMooreComplexMap (relFree P)).id n
  have r : Retract ((source P).X n) (ModuleCat.of ℤ (level P (op ⦋n⦌))) :=
    ⟨integralModules.map i,integralModules.map p,by rw [← integralModules.map_comp,h]; exact integralModules.map_id _⟩
  let : Projective (ModuleCat.of ℤ (level P (op ⦋n⦌))) := (IsProjective.iff_projective (R:=ℤ) _).mp inferInstance
  exact r.projective

def onClasses : NativeRelativeMorphism P A →ₗ[ℤ] ChainClasses.classes (source P) (target A) :=
  (ChainClasses.nullMaps _ _).mkQ.comp ((integralChains.mapAddHom (X:=relFree P) (Y:=A)).toIntLinearMap.comp
    (relativeFreeEquiv P A).toIntLinearEquiv.toLinearMap)

theorem onClasses_eq_iff (f g : NativeRelativeMorphism P A) :
    onClasses P A f=onClasses P A g ↔ f.homotopyClass=g.homotopyClass := by
  rw [homotopyClass_eq_iff,native_homotopy_iff]
  change (Submodule.Quotient.mk _ : ChainClasses.classes (source P) (target A))=Submodule.Quotient.mk _ ↔ _
  rw [ChainClasses.class_eq_iff]
  exact ⟨Nonempty.map integralModules.preimageHomotopy,Nonempty.map integralModules.mapHomotopy⟩

theorem onClasses_surjective : Function.Surjective (onClasses P A) := by
  intro x
  obtain ⟨u,rfl⟩ := (ChainClasses.nullMaps (source P) (target A)).mkQ_surjective x
  obtain ⟨v,hv⟩ := integralChains.map_surjective u
  obtain ⟨f,hf⟩ := (relativeFreeEquiv P A).surjective v
  exact ⟨f,congrArg Submodule.Quotient.mk ((congrArg integralChains.map hf).trans hv)⟩

private theorem kernel_eq : NativeNullMaps P A=LinearMap.ker (onClasses P A) := by
  ext f
  change homotopyClassLinear P A f=0 ↔ onClasses P A f=0
  rw [← (homotopyClassLinear P A).map_zero,← (onClasses P A).map_zero]
  exact (onClasses_eq_iff P A f 0).symm

def nativeChainClasses : NativeHomotopyClass P A ≃ₗ[ℤ] ChainClasses.classes (source P) (target A) :=
  (quotientNativeNullEquiv P A).symm.trans ((Submodule.quotEquivOfEq _ _ (kernel_eq P A)).trans
    ((onClasses P A).quotKerEquivOfSurjective (onClasses_surjective P A)))

theorem nativeChainClasses_mk (f : NativeRelativeMorphism P A) :
    nativeChainClasses P A f.homotopyClass=onClasses P A f := by
  rw [← quotientNativeNullEquiv_mkQ P A f]
  simp only [nativeChainClasses,LinearEquiv.trans_apply,LinearEquiv.symm_apply_apply]
  rfl

/-- A homology generator of the pair induces an evaluation equivalence for
every simplicial abelian target. -/
def nativeEvaluation (n : ℕ) (z : ChainSphere.cycles (source P) n)
    (hz : QuasiIso (ChainSphere.mapOfCycle (source P) n z)) :
    NativeHomotopyClass P A ≃ₗ[ℤ] (target A).homology n :=
  (nativeChainClasses P A).trans (fundamentalEvaluation _ _ n z hz)

theorem nativeEvaluation_mk (n : ℕ) (z : ChainSphere.cycles (source P) n)
    (hz : QuasiIso (ChainSphere.mapOfCycle (source P) n z)) (f : NativeRelativeMorphism P A) :
    nativeEvaluation P A n z hz f.homotopyClass=ChainSphere.mapClassesEquivHomology _ n
      (Submodule.Quotient.mk (ChainSphere.mapOfCycle (source P) n z ≫ integralChains.map (linearize P A f))) := by
  rw [nativeEvaluation,LinearEquiv.trans_apply,nativeChainClasses_mk]
  exact fundamentalEvaluation_mk (source P) (target A) n z hz (integralChains.map (linearize P A f))

end GeneralSphereT.Transport.RelativeChains

