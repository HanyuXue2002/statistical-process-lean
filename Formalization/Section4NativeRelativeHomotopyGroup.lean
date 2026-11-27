import Formalization.Section4RelativeMappingGroups
import Mathlib.AlgebraicTopology.SimplicialSet.Homotopy

set_option linter.style.header false

/-!
# Section 4: the abelian group of native relative homotopy classes

For a simplicial abelian target, pointwise addition, zero, and negation
preserve relative simplicial homotopies with zero boundary.  Consequently
Mathlib's native `SSet.RelativeMorphism.HomotopyClass` is an abelian group,
and the quotient map from relative morphisms is additive.

This is the missing bridge needed to use actual simplicial homotopy classes,
rather than an abstract quotient by a postulated subgroup, as the target of
the comparisons in Section 4.
-/

noncomputable section

open CategoryTheory CategoryTheory.Category Opposite Simplicial
open MonoidalCategory CartesianMonoidalCategory

namespace GeneralSphereT.Section4
namespace NativeRelativeHomotopyGroup

universe u

open UnderlyingSSet
open RelativeMapping

variable {X W : SSet.{u}} (P : X.Subcomplex)
variable (A : SimplicialObject AddCommGrpCat.{u})

/-- Native relative maps with the constant zero boundary. -/
abbrev NativeRelativeMorphism :=
  SSet.RelativeMorphism P (zeroSubcomplex A) (zeroBoundary P A)

/-- Their actual relative simplicial homotopy classes. -/
abbrev NativeHomotopyClass :=
  SSet.RelativeMorphism.HomotopyClass
    P (zeroSubcomplex A) (zeroBoundary P A)

@[simp]
theorem relativeMorphism_zero_map :
    (0 : NativeRelativeMorphism P A).map =
      (0 : X ⟶ underlyingSSet A) :=
  rfl

@[simp]
theorem relativeMorphism_add_map (f g : NativeRelativeMorphism P A) :
    (f + g).map = f.map + g.map :=
  rfl

@[simp]
theorem relativeMorphism_neg_map (f : NativeRelativeMorphism P A) :
    (-f).map = -f.map :=
  rfl

@[simp]
theorem map_add_app_apply (f g : W ⟶ underlyingSSet A)
    (Δ : SimplexCategoryᵒᵖ) (x : W.obj Δ) :
    (f + g).app Δ x = f.app Δ x + g.app Δ x :=
  rfl

@[simp]
theorem map_neg_app_apply (f : W ⟶ underlyingSSet A)
    (Δ : SimplexCategoryᵒᵖ) (x : W.obj Δ) :
    (-f).app Δ x = -f.app Δ x :=
  rfl

/-- Precomposition distributes over pointwise addition. -/
theorem comp_addMap (k : W ⟶ X)
    (f g : X ⟶ underlyingSSet A) :
    k ≫ (f + g) = (k ≫ f) + (k ≫ g) := by
  ext Δ x
  rfl

/-- Precomposition commutes with pointwise negation. -/
theorem comp_negMap (k : W ⟶ X) (f : X ⟶ underlyingSSet A) :
    k ≫ (-f) = -(k ≫ f) := by
  ext Δ x
  rfl

/-- Precomposition distributes over pointwise subtraction. -/
theorem comp_subMap (k : W ⟶ X)
    (f g : X ⟶ underlyingSSet A) :
    k ≫ (f - g) = (k ≫ f) - (k ≫ g) := by
  rw [sub_eq_add_neg, comp_addMap, comp_negMap]
  exact (sub_eq_add_neg _ _).symm

/-- The relative zero boundary, pulled back along the cylinder projection,
is still the zero map. -/
theorem cylinder_zeroBoundary :
    fst (P : SSet) Δ[1] ≫ zeroBoundary P A ≫ (zeroSubcomplex A).ι =
      (0 : (P : SSet) ⊗ Δ[1] ⟶ underlyingSSet A) := by
  rw [zeroBoundary_comp_inclusion]
  ext Δ x
  rfl

/-- Pointwise addition of native relative simplicial homotopies. -/
def homotopyAdd
    {f₀ f₁ g₀ g₁ : NativeRelativeMorphism P A}
    (Hf : SSet.RelativeMorphism.Homotopy f₀ f₁)
    (Hg : SSet.RelativeMorphism.Homotopy g₀ g₁) :
    SSet.RelativeMorphism.Homotopy (f₀ + g₀) (f₁ + g₁) where
  h := Hf.h + Hg.h
  h₀ := by
    rw [comp_addMap, Hf.h₀, Hg.h₀]
    rfl
  h₁ := by
    rw [comp_addMap, Hf.h₁, Hg.h₁]
    rfl
  rel := by
    rw [comp_addMap, Hf.rel, Hg.rel, cylinder_zeroBoundary,
      zero_add]

/-- Pointwise negation of a native relative simplicial homotopy. -/
def homotopyNeg
    {f₀ f₁ : NativeRelativeMorphism P A}
    (H : SSet.RelativeMorphism.Homotopy f₀ f₁) :
    SSet.RelativeMorphism.Homotopy (-f₀) (-f₁) where
  h := -H.h
  h₀ := by
    rw [comp_negMap, H.h₀]
    rfl
  h₁ := by
    rw [comp_negMap, H.h₁]
    rfl
  rel := by
    rw [comp_negMap, H.rel, cylinder_zeroBoundary, neg_zero]

/-- Pointwise subtraction of native relative simplicial homotopies. -/
def homotopySub
    {f₀ f₁ g₀ g₁ : NativeRelativeMorphism P A}
    (Hf : SSet.RelativeMorphism.Homotopy f₀ f₁)
    (Hg : SSet.RelativeMorphism.Homotopy g₀ g₁) :
    SSet.RelativeMorphism.Homotopy (f₀ - g₀) (f₁ - g₁) := by
  simpa only [sub_eq_add_neg] using homotopyAdd P A Hf (homotopyNeg P A Hg)

/-! ## Elementary homotopy is already an equivalence relation

For a general simplicial target, cylinder homotopy need not be symmetric or
transitive.  An abelian target removes that obstruction: reversing `H` is
the affine homotopy `f + g - H`, and composing `H` with `K` is
`H + K - g`.  Thus equality in Mathlib's `Quot` can be represented by one
actual relative cylinder homotopy in this setting.
-/

/-- A relative map, held constant along the cylinder, is zero on the
relative subcomplex. -/
theorem relativeMorphism_fst_comp_map_eq_zero
    (f : NativeRelativeMorphism P A) :
    P.ι ▷ Δ[1] ≫ fst X Δ[1] ≫ f.map =
      (0 : (P : SSet) ⊗ Δ[1] ⟶ underlyingSSet A) := by
  calc
    P.ι ▷ Δ[1] ≫ fst X Δ[1] ≫ f.map =
        (P.ι ▷ Δ[1] ≫ fst X Δ[1]) ≫ f.map :=
      (Category.assoc _ _ _).symm
    _ = (fst (P : SSet) Δ[1] ≫ P.ι) ≫ f.map := by
      rw [whiskerRight_fst]
    _ = fst (P : SSet) Δ[1] ≫ (P.ι ≫ f.map) :=
      Category.assoc _ _ _
    _ = fst (P : SSet) Δ[1] ≫
        (zeroBoundary P A ≫ (zeroSubcomplex A).ι) := by rw [f.comm]
    _ = fst (P : SSet) Δ[1] ≫ zeroBoundary P A ≫
        (zeroSubcomplex A).ι := (Category.assoc _ _ _).symm
    _ = 0 := cylinder_zeroBoundary P A

/-- Reverse an actual relative homotopy into a simplicial abelian target. -/
def homotopySymm
    {f g : NativeRelativeMorphism P A}
    (H : SSet.RelativeMorphism.Homotopy f g) :
    SSet.RelativeMorphism.Homotopy g f where
  h := (fst X Δ[1] ≫ f.map) + (fst X Δ[1] ≫ g.map) - H.h
  h₀ := by
    rw [comp_subMap, comp_addMap, H.h₀]
    have hf : SSet.ι₀ ≫ fst X Δ[1] ≫ f.map = f.map := by
      rw [← Category.assoc, SSet.ι₀_fst, Category.id_comp]
    have hg : SSet.ι₀ ≫ fst X Δ[1] ≫ g.map = g.map := by
      rw [← Category.assoc, SSet.ι₀_fst, Category.id_comp]
    rw [hf, hg]
    exact add_sub_cancel_left f.map g.map
  h₁ := by
    rw [comp_subMap, comp_addMap, H.h₁]
    have hf : SSet.ι₁ ≫ fst X Δ[1] ≫ f.map = f.map := by
      rw [← Category.assoc, SSet.ι₁_fst, Category.id_comp]
    have hg : SSet.ι₁ ≫ fst X Δ[1] ≫ g.map = g.map := by
      rw [← Category.assoc, SSet.ι₁_fst, Category.id_comp]
    rw [hf, hg]
    exact add_sub_cancel_right f.map g.map
  rel := by
    rw [comp_subMap, comp_addMap,
      relativeMorphism_fst_comp_map_eq_zero P A f,
      relativeMorphism_fst_comp_map_eq_zero P A g,
      H.rel, cylinder_zeroBoundary, zero_add, sub_self]

/-- Compose two actual relative homotopies into a simplicial abelian
target. -/
def homotopyTrans
    {f g h : NativeRelativeMorphism P A}
    (H : SSet.RelativeMorphism.Homotopy f g)
    (K : SSet.RelativeMorphism.Homotopy g h) :
    SSet.RelativeMorphism.Homotopy f h where
  h := H.h + K.h - (fst X Δ[1] ≫ g.map)
  h₀ := by
    rw [comp_subMap, comp_addMap, H.h₀, K.h₀]
    have hg : SSet.ι₀ ≫ fst X Δ[1] ≫ g.map = g.map := by
      rw [← Category.assoc, SSet.ι₀_fst, Category.id_comp]
    rw [hg]
    exact add_sub_cancel_right f.map g.map
  h₁ := by
    rw [comp_subMap, comp_addMap, H.h₁, K.h₁]
    have hg : SSet.ι₁ ≫ fst X Δ[1] ≫ g.map = g.map := by
      rw [← Category.assoc, SSet.ι₁_fst, Category.id_comp]
    rw [hg]
    exact add_sub_cancel_left g.map h.map
  rel := by
    rw [comp_subMap, comp_addMap, H.rel, K.rel,
      relativeMorphism_fst_comp_map_eq_zero P A g,
      cylinder_zeroBoundary, zero_add, sub_zero]

/-! ## Operations on the native quotient -/

/-- Zero native relative homotopy class. -/
def homotopyClassZero : NativeHomotopyClass P A :=
  (0 : NativeRelativeMorphism P A).homotopyClass

/-- Addition of native relative homotopy classes. -/
def homotopyClassAdd :
    NativeHomotopyClass P A →
      NativeHomotopyClass P A → NativeHomotopyClass P A :=
  Quot.map₂
    (fun f g : NativeRelativeMorphism P A ↦ f + g)
    (fun f _g₀ _g₁ ⟨Hg⟩ ↦
      ⟨homotopyAdd P A
        (SSet.RelativeMorphism.Homotopy.refl f) Hg⟩)
    (fun _f₀ _f₁ g ⟨Hf⟩ ↦
      ⟨homotopyAdd P A Hf
        (SSet.RelativeMorphism.Homotopy.refl g)⟩)

/-- Negation of native relative homotopy classes. -/
def homotopyClassNeg :
    NativeHomotopyClass P A → NativeHomotopyClass P A :=
  Quot.map (fun f : NativeRelativeMorphism P A ↦ -f)
    (fun _ _ ⟨H⟩ ↦ ⟨homotopyNeg P A H⟩)

instance : Zero (NativeHomotopyClass P A) :=
  ⟨homotopyClassZero P A⟩

instance : Add (NativeHomotopyClass P A) :=
  ⟨homotopyClassAdd P A⟩

instance : Neg (NativeHomotopyClass P A) :=
  ⟨homotopyClassNeg P A⟩

@[simp]
theorem homotopyClass_zero :
    (0 : NativeRelativeMorphism P A).homotopyClass =
      (0 : NativeHomotopyClass P A) :=
  rfl

@[simp]
theorem homotopyClass_add (f g : NativeRelativeMorphism P A) :
    (f + g).homotopyClass = f.homotopyClass + g.homotopyClass :=
  rfl

@[simp]
theorem homotopyClass_neg (f : NativeRelativeMorphism P A) :
    (-f).homotopyClass = -f.homotopyClass :=
  rfl

/-- Native relative homotopy classes into a simplicial abelian group form an
abelian group. -/
instance nativeHomotopyClassAddCommGroup :
    AddCommGroup (NativeHomotopyClass P A) where
  add_assoc x y z := by
    refine Quot.inductionOn x ?_
    intro f
    refine Quot.inductionOn y ?_
    intro g
    refine Quot.inductionOn z ?_
    intro h
    exact congrArg SSet.RelativeMorphism.homotopyClass (add_assoc f g h)
  zero_add x := by
    refine Quot.inductionOn x ?_
    intro f
    exact congrArg SSet.RelativeMorphism.homotopyClass (zero_add f)
  add_zero x := by
    refine Quot.inductionOn x ?_
    intro f
    exact congrArg SSet.RelativeMorphism.homotopyClass (add_zero f)
  neg_add_cancel x := by
    refine Quot.inductionOn x ?_
    intro f
    exact congrArg SSet.RelativeMorphism.homotopyClass (neg_add_cancel f)
  add_comm x y := by
    refine Quot.inductionOn x ?_
    intro f
    refine Quot.inductionOn y ?_
    intro g
    exact congrArg SSet.RelativeMorphism.homotopyClass (add_comm f g)
  nsmul := nsmulRec
  zsmul := zsmulRec

/-- For a simplicial abelian target, equality of native relative homotopy
classes is represented by one actual cylinder homotopy.  Mathlib defines
the class type using the equivalence closure of elementary homotopy; the
affine symmetry and transitivity constructions above collapse that closure
back to a single elementary homotopy. -/
theorem nonempty_homotopy_of_homotopyClass_eq
    {f g : NativeRelativeMorphism P A}
    (h : f.homotopyClass = g.homotopyClass) :
    Nonempty (SSet.RelativeMorphism.Homotopy f g) := by
  let r := fun f g : NativeRelativeMorphism P A ↦
    Nonempty (SSet.RelativeMorphism.Homotopy f g)
  have hgen : Relation.EqvGen r f g := (Quot.eq).mp h
  exact Relation.EqvGen.rec
    (motive := fun x y _ ↦
      Nonempty (SSet.RelativeMorphism.Homotopy x y))
    (fun _ _ hfg ↦ hfg)
    (fun x ↦ ⟨SSet.RelativeMorphism.Homotopy.refl x⟩)
    (fun _ _ _ ih ↦ by
      rcases ih with ⟨H⟩
      exact ⟨homotopySymm P A H⟩)
    (fun _ _ _ _ _ ih₁ ih₂ ↦ by
      rcases ih₁ with ⟨H⟩
      rcases ih₂ with ⟨K⟩
      exact ⟨homotopyTrans P A H K⟩)
    hgen

/-- Characterization of equality of native relative homotopy classes by
one actual relative cylinder homotopy. -/
theorem homotopyClass_eq_iff
    {f g : NativeRelativeMorphism P A} :
    f.homotopyClass = g.homotopyClass ↔
      Nonempty (SSet.RelativeMorphism.Homotopy f g) := by
  constructor
  · exact nonempty_homotopy_of_homotopyClass_eq P A
  · rintro ⟨H⟩
    exact H.eq

/-- The native quotient map is an additive homomorphism. -/
def homotopyClassHom :
    NativeRelativeMorphism P A →+
      NativeHomotopyClass P A where
  toFun := SSet.RelativeMorphism.homotopyClass
  map_zero' := homotopyClass_zero P A
  map_add' := homotopyClass_add P A

@[simp]
theorem homotopyClassHom_apply (f : NativeRelativeMorphism P A) :
    homotopyClassHom P A f = f.homotopyClass :=
  rfl

/-- The native homotopy-class quotient as a `ℤ`-linear map. -/
def homotopyClassLinear :
    NativeRelativeMorphism P A →ₗ[ℤ]
      NativeHomotopyClass P A :=
  (homotopyClassHom P A).toIntLinearMap

/-- Every native homotopy class has a representative. -/
theorem homotopyClassLinear_surjective :
    Function.Surjective (homotopyClassLinear P A) := by
  intro x
  rcases x.eq_homotopyClass with ⟨f, rfl⟩
  exact ⟨f, rfl⟩

/-- The actual subgroup of native relative maps representing the zero
homotopy class. -/
abbrev NativeNullMaps : Submodule ℤ (NativeRelativeMorphism P A) :=
  LinearMap.ker (homotopyClassLinear P A)

/-- The quotient by genuinely nullhomotopic native maps is the native
relative homotopy-class group itself. -/
def quotientNativeNullEquiv :
    (NativeRelativeMorphism P A ⧸ NativeNullMaps P A) ≃ₗ[ℤ]
      NativeHomotopyClass P A :=
  (homotopyClassLinear P A).quotKerEquivOfSurjective
    (homotopyClassLinear_surjective P A)

@[simp]
theorem quotientNativeNullEquiv_mkQ
    (f : NativeRelativeMorphism P A) :
    quotientNativeNullEquiv P A ((NativeNullMaps P A).mkQ f) =
      f.homotopyClass := by
  exact LinearMap.quotKerEquivOfSurjective_apply_mk
    (homotopyClassLinear P A)
    (homotopyClassLinear_surjective P A) f

/-- The native quotient map, transported back to the strictly-zero map
model used by the algebraic part of Section 4. -/
def strictHomotopyClassLinear :
    RelativeZeroMaps P A →ₗ[ℤ] NativeHomotopyClass P A :=
  (homotopyClassLinear P A).comp
    (relativeMorphismAddEquiv P A).toIntLinearEquiv.toLinearMap

@[simp]
theorem strictHomotopyClassLinear_apply (f : RelativeZeroMaps P A) :
    strictHomotopyClassLinear P A f =
      (RelativeZeroMaps.toRelativeMorphism P A f).homotopyClass :=
  rfl

/-- Every native class also has a strictly-zero representative. -/
theorem strictHomotopyClassLinear_surjective :
    Function.Surjective (strictHomotopyClassLinear P A) := by
  intro x
  rcases homotopyClassLinear_surjective P A x with ⟨f, rfl⟩
  refine ⟨(relativeMorphismAddEquiv P A).symm f, ?_⟩
  change ((relativeMorphismAddEquiv P A)
    ((relativeMorphismAddEquiv P A).symm f)).homotopyClass =
      f.homotopyClass
  rw [(relativeMorphismAddEquiv P A).apply_symm_apply]

/-- Strictly-zero maps which represent the zero native relative homotopy
class. -/
abbrev StrictNullMaps : Submodule ℤ (RelativeZeroMaps P A) :=
  LinearMap.ker (strictHomotopyClassLinear P A)

/-- Actual native homotopy classes as a quotient of the strictly-zero maps
used on the algebraic side. -/
def quotientStrictNullEquiv :
    (RelativeZeroMaps P A ⧸ StrictNullMaps P A) ≃ₗ[ℤ]
      NativeHomotopyClass P A :=
  (strictHomotopyClassLinear P A).quotKerEquivOfSurjective
    (strictHomotopyClassLinear_surjective P A)

@[simp]
theorem quotientStrictNullEquiv_mkQ (f : RelativeZeroMaps P A) :
    quotientStrictNullEquiv P A ((StrictNullMaps P A).mkQ f) =
      (RelativeZeroMaps.toRelativeMorphism P A f).homotopyClass := by
  exact LinearMap.quotKerEquivOfSurjective_apply_mk
    (strictHomotopyClassLinear P A)
    (strictHomotopyClassLinear_surjective P A) f

/-- Pointwise subtraction descends to the expected subtraction of native
homotopy classes. -/
@[simp]
theorem homotopyClass_sub (f g : NativeRelativeMorphism P A) :
    (f - g).homotopyClass = f.homotopyClass - g.homotopyClass := by
  calc
    (f - g).homotopyClass =
        f.homotopyClass + (-g).homotopyClass := by
      simpa only [sub_eq_add_neg] using homotopyClass_add P A f (-g)
    _ = f.homotopyClass + -g.homotopyClass := by
      rw [homotopyClass_neg]
    _ = f.homotopyClass - g.homotopyClass :=
      (sub_eq_add_neg _ _).symm

end NativeRelativeHomotopyGroup
end GeneralSphereT.Section4
