import Formalization.Section4NativeRelativeHomotopyGroup
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-! Free integral chains on a simplicial pair before normalization.
The generators in the boundary subcomplex are zero in every degree. -/
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
noncomputable section
open CategoryTheory CategoryTheory.Category Opposite Simplicial
open GeneralSphereT.Section4 GeneralSphereT.Section4.RelativeMapping
open GeneralSphereT.Section4.NativeRelativeHomotopyGroup
namespace GeneralSphereT.Transport.RelativeChains
universe u
variable {X Y : SSet.{u}} (P : X.Subcomplex) (Q : Y.Subcomplex)
abbrev level (Δ : SimplexCategoryᵒᵖ) := {x : X.obj Δ // x ∉ P.obj Δ} →₀ ℤ
def symbol {Δ : SimplexCategoryᵒᵖ} (x : X.obj Δ) : level P Δ := by
  classical
  exact if h : x ∈ P.obj Δ then 0 else Finsupp.single ⟨x,h⟩ 1

theorem symbol_boundary {Δ} (x : X.obj Δ) (hx : x ∈ P.obj Δ) : symbol P x=0 := by
  classical
  simp [symbol,hx]

def liftLevel {Δ} {B : AddCommGrpCat.{u}} (f : X.obj Δ → B) :
    AddCommGrpCat.of (level P Δ) ⟶ B :=
  AddCommGrpCat.ofHom (Finsupp.linearCombination ℤ (fun x : {x : X.obj Δ // x ∉ P.obj Δ} => f x.val)).toAddMonoidHom

theorem lift_symbol {Δ} {B : AddCommGrpCat.{u}} (f : X.obj Δ → B)
    (hf : ∀ x ∈ P.obj Δ, f x=0) (x : X.obj Δ) : liftLevel P f (symbol P x)=f x := by
  classical
  by_cases h : x ∈ P.obj Δ
  · rw [symbol_boundary P x h,map_zero,hf x h]
  · change Finsupp.linearCombination ℤ _ (symbol P x)=_
    simp [symbol,h]

theorem level_ext {Δ} {B : AddCommGrpCat.{u}} {f g : AddCommGrpCat.of (level P Δ) ⟶ B}
    (h : ∀ x : X.obj Δ, f (symbol P x)=g (symbol P x)) : f=g := by
  have he : f.hom.toIntLinearMap=g.hom.toIntLinearMap := by
    apply Finsupp.lhom_ext'
    intro x
    apply LinearMap.ext_ring
    simpa [symbol,x.property] using h x.val
  apply AddCommGrpCat.ext
  exact LinearMap.congr_fun he

def restriction {Δ Δ'} (θ : Δ ⟶ Δ') : AddCommGrpCat.of (level P Δ) ⟶ AddCommGrpCat.of (level P Δ') :=
  liftLevel P (fun x => symbol P (X.map θ x))

@[simp] theorem restriction_symbol {Δ Δ'} (θ : Δ ⟶ Δ') (x : X.obj Δ) :
    restriction P θ (symbol P x)=symbol P (X.map θ x) :=
  lift_symbol P _ (fun x hx => symbol_boundary P _ (P.map θ hx)) x

abbrev relFree : SimplicialObject AddCommGrpCat.{u} where
  obj Δ := AddCommGrpCat.of (level P Δ)
  map := restriction P
  map_id Δ := by
    apply level_ext P
    intro x
    change restriction P (𝟙 Δ) (symbol P x)=symbol P x
    rw [restriction_symbol,X.map_id]
    rfl
  map_comp θ φ := by
    apply level_ext P
    intro x
    change restriction P (θ ≫ φ) (symbol P x)=restriction P φ (restriction P θ (symbol P x))
    rw [restriction_symbol,restriction_symbol,restriction_symbol,X.map_comp]
    rfl

def relMap (f : X ⟶ Y) (hf : ∀ Δ (x : X.obj Δ), x ∈ P.obj Δ → f.app Δ x ∈ Q.obj Δ) :
    relFree P ⟶ relFree Q where
  app Δ := liftLevel P (fun x => symbol Q (f.app Δ x))
  naturality Δ Δ' θ := by
    apply level_ext P
    intro x
    change liftLevel P (fun y => symbol Q (f.app Δ' y)) (restriction P θ (symbol P x)) = restriction Q θ (liftLevel P (fun y => symbol Q (f.app Δ y)) (symbol P x))
    have h (D : SimplexCategoryᵒᵖ) := lift_symbol (B:=AddCommGrpCat.of (level Q D)) P (fun x => symbol Q (f.app D x)) (fun x hx => symbol_boundary Q _ (hf D x hx))
    rw [restriction_symbol,h,h,restriction_symbol]
    exact congrArg (symbol Q) (f.naturality_apply θ x)

@[simp] theorem relMap_symbol (f : X ⟶ Y) (hf : ∀ Δ (x : X.obj Δ), x ∈ P.obj Δ → f.app Δ x ∈ Q.obj Δ) {Δ} (x : X.obj Δ) :
    (relMap P Q f hf).app Δ (symbol P x)=symbol Q (f.app Δ x) :=
  lift_symbol (B:=AddCommGrpCat.of (level Q Δ)) P (fun x => symbol Q (f.app Δ x)) (fun x hx => symbol_boundary Q _ (hf Δ x hx)) x

variable (A : SimplicialObject AddCommGrpCat.{u})

theorem zero_on_boundary (f : NativeRelativeMorphism P A) {Δ} (x : X.obj Δ) (hx : x ∈ P.obj Δ) :
    f.map.app Δ x=0 := by
  have e := f.comm.trans (zeroBoundary_comp_inclusion P A)
  exact ConcreteCategory.congr_hom (NatTrans.congr_app e Δ) ⟨x,hx⟩

def linearize (f : NativeRelativeMorphism P A) : relFree P ⟶ A where
  app Δ := liftLevel P (fun x => f.map.app Δ x)
  naturality Δ Δ' θ := by
    apply level_ext P
    intro x
    change liftLevel P _ (restriction P θ (symbol P x))=A.map θ (liftLevel P _ (symbol P x))
    have h (D) := lift_symbol P (fun x => f.map.app D x) (zero_on_boundary P A f)
    rw [restriction_symbol,h,h]
    exact f.map.naturality_apply θ x

@[simp] theorem linearize_symbol (f : NativeRelativeMorphism P A) {Δ} (x : X.obj Δ) :
    (linearize P A f).app Δ (symbol P x)=f.map.app Δ x := lift_symbol P _ (zero_on_boundary P A f) x

def onSymbols (f : relFree P ⟶ A) : NativeRelativeMorphism P A where
  map := {
    app := fun Δ => ↾fun x => f.app Δ (symbol P x)
    naturality := by
      intro Δ Δ' θ
      ext x
      exact (congrArg (f.app Δ') (restriction_symbol P θ x).symm).trans
        (ConcreteCategory.congr_hom (f.naturality θ) (symbol P x)) }
  comm := by
    rw [zeroBoundary_comp_inclusion]
    ext Δ x
    change f.app Δ (symbol P x.val)=0
    rw [symbol_boundary P x.val x.property,map_zero]

def relativeFreeEquiv : NativeRelativeMorphism P A ≃+ (relFree P ⟶ A) where
  toFun := linearize P A
  invFun := onSymbols P A
  left_inv f := by
    apply SSet.RelativeMorphism.ext
    ext Δ x
    exact linearize_symbol P A f x
  right_inv f := by
    ext1 Δ
    apply level_ext P
    intro x
    exact linearize_symbol P A _ x
  map_add' f g := by
    ext1 Δ
    apply level_ext P
    intro x
    change _ = (linearize P A f).app Δ (symbol P x)+(linearize P A g).app Δ (symbol P x)
    exact (linearize_symbol P A (f+g) x).trans (congrArg₂ (·+·) (linearize_symbol P A f x).symm (linearize_symbol P A g x).symm)

end GeneralSphereT.Transport.RelativeChains
