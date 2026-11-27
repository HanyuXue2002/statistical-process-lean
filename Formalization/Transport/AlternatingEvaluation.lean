import Formalization.Transport.RelativeEvaluation
import Formalization.Transport.OrientedConeCycle

/-! Compute native evaluation in the alternating face complex, where signed
spatial simplices and the lifted prism are given explicitly. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open CategoryTheory HomologicalComplex AlgebraicTopology AlgebraicTopology.DoldKan
open GeneralSphereT.Section4.NativeRelativeHomotopyGroup OpenDisk
namespace GeneralSphereT.Transport.RelativeChains
section
variable {R : Type} [CommRing R] {C D B : ChainComplex (ModuleCat R) ℕ}

private def post (k : D ⟶ B) : (C ⟶ D) →ₗ[R] (C ⟶ B) where
  toFun f := f ≫ k
  map_add' f g := by simp only [Preadditive.add_comp]
  map_smul' r f := by simp only [Linear.smul_comp,RingHom.id_apply]

private def postClasses (k : D ⟶ B) : ChainClasses.classes C D →ₗ[R] ChainClasses.classes C B :=
  (ChainClasses.nullMaps C D).mapQ (ChainClasses.nullMaps C B) (post k) (by
    rintro f ⟨H⟩
    exact ⟨by simpa [post] using H.compRight k⟩)

private def changeTarget (e : HomotopyEquiv D B) : ChainClasses.classes C D ≃ₗ[R] ChainClasses.classes C B where
  toLinearMap := postClasses e.hom
  invFun := postClasses e.inv
  left_inv x := by
    obtain ⟨f,rfl⟩ := (ChainClasses.nullMaps C D).mkQ_surjective x
    apply (ChainClasses.class_eq_iff C D).mpr
    change Nonempty (Homotopy ((f ≫ e.hom) ≫ e.inv) f)
    exact ⟨by simpa only [Category.assoc] using e.homotopyHomInvId.compLeftId f⟩
  right_inv x := by
    obtain ⟨f,rfl⟩ := (ChainClasses.nullMaps C B).mkQ_surjective x
    apply (ChainClasses.class_eq_iff C B).mpr
    change Nonempty (Homotopy ((f ≫ e.inv) ≫ e.hom) f)
    exact ⟨by simpa only [Category.assoc] using e.homotopyInvHomId.compLeftId f⟩

def imageCycle (n : ℕ) (f : C ⟶ D) (z : ChainSphere.cycles C n) : ChainSphere.cycles D n :=
  ⟨f.f n z.val,by
    have e := ConcreteCategory.congr_hom (f.comm n (n-1)) z.val
    exact e.trans ((congrArg (f.f (n-1)) z.property).trans (map_zero _))⟩

end

abbrev altChains := (alternatingFaceMapComplex AddCommGrpCat.{0}) ⋙ integralModules.mapHomologicalComplex (.down ℕ)

def normalization (A : SimplicialObject AddCommGrpCat.{0}) : HomotopyEquiv (integralChains.obj A) (altChains.obj A) :=
  integralModules.mapHomotopyEquiv (homotopyEquivNormalizedMooreComplexAlternatingFaceMapComplex (Y:=A))

variable {X : SSet.{0}} (P : X.Subcomplex) (A : SimplicialObject AddCommGrpCat.{0})

def nativeAltClasses : NativeHomotopyClass P A ≃ₗ[ℤ] ChainClasses.classes (altChains.obj (relFree P)) (altChains.obj A) :=
  (nativeChainClasses P A).trans ((ChainClasses.equivOfHomotopyEquiv (normalization (relFree P))).trans (changeTarget (normalization A)))

theorem nativeAltClasses_mk (f : NativeRelativeMorphism P A) :
    nativeAltClasses P A f.homotopyClass=Submodule.Quotient.mk (altChains.map (linearize P A f)) := by
  rw [nativeAltClasses,LinearEquiv.trans_apply,nativeChainClasses_mk]
  let k := linearize P A f
  let C := altChains.obj (relFree P)
  let D := altChains.obj A
  change (Submodule.Quotient.mk (((normalization (relFree P)).inv ≫ integralChains.map k) ≫ (normalization A).hom) : ChainClasses.classes C D) = _
  apply (ChainClasses.class_eq_iff C D).mpr
  have nat : integralChains.map k ≫ (normalization A).hom = (normalization (relFree P)).hom ≫ altChains.map k := by
    let T := integralModules.mapHomologicalComplex (.down ℕ)
    exact (T.map_comp _ _).symm.trans ((T.congr_map ((inclusionOfMooreComplex AddCommGrpCat).naturality k)).trans (T.map_comp _ _))
  rw [Category.assoc,nat,← Category.assoc]
  exact ⟨(normalization (relFree P)).homotopyInvHomId.compRightId _⟩

instance altProjective (n : ℕ) : Projective ((altChains.obj (relFree P)).X n) :=
  (IsProjective.iff_projective (R:=ℤ) (level P _)).mp inferInstance

def altEvaluation (n : ℕ) (z : ChainSphere.cycles (altChains.obj (relFree P)) n)
    (hz : QuasiIso (ChainSphere.mapOfCycle _ n z)) :
    NativeHomotopyClass P A ≃ₗ[ℤ] (altChains.obj A).homology n :=
  (nativeAltClasses P A).trans (fundamentalEvaluation _ _ n z hz)

theorem altEvaluation_mk (n : ℕ) (z : ChainSphere.cycles (altChains.obj (relFree P)) n)
    (hz : QuasiIso (ChainSphere.mapOfCycle _ n z)) (f : NativeRelativeMorphism P A) :
    altEvaluation P A n z hz f.homotopyClass=ChainSphere.homologyQuotientEquiv _ n (Submodule.Quotient.mk
      (imageCycle n (altChains.map (linearize P A f)) z)) := by
  rw [altEvaluation,LinearEquiv.trans_apply,nativeAltClasses_mk,fundamentalEvaluation_mk]
  let k := altChains.map (linearize P A f)
  apply congrArg (ChainSphere.homologyQuotientEquiv _ n)
  apply congrArg Submodule.Quotient.mk
  apply Subtype.ext
  exact congrArg (k.f n) (congrArg Subtype.val (ChainSphere.evaluation_mapOfCycle _ n z))

end GeneralSphereT.Transport.RelativeChains

