import Formalization.Section4NativeSimplicialCone

set_option linter.style.header false

/-!
# Section 4: the native two-cone difference map

The suspension is defined as the pushout of two copies of the categorical
cone along their common bottom.  For a source subcomplex `P`, a pointed
suspension map is required to vanish on the copy of `P ⊗ Δ[1]` in each
cone.  Subtracting the upper-cone restriction from the lower-cone
restriction then gives an actual map of the cone which vanishes on the pair
consisting of its bottom and `P ⊗ Δ[1]`.

We construct this as a surjective linear map to Mathlib's native relative
homotopy-class group.  Therefore its quotient by its actual kernel is
canonically equivalent to that group.  The only remaining suspension input
is the standard assertion that this kernel is precisely the subgroup of
nullhomotopic pointed suspension maps.
-/

noncomputable section

open CategoryTheory CategoryTheory.Category Opposite Simplicial
open MonoidalCategory CartesianMonoidalCategory Limits

namespace GeneralSphereT.Section4
namespace NativeDoubleCone

universe u

open UnderlyingSSet
open RelativeMapping
open NativeRelativeHomotopyGroup
open NativeSimplicialCone

variable {X W : SSet.{u}}

/-- The suspension obtained by gluing two copies of `cone X` along `X`. -/
abbrev suspension (X : SSet.{u}) : SSet.{u} :=
  pushout (bottomInclusion X) (bottomInclusion X)

/-- Inclusion of the lower cone. -/
abbrev lowerConeInclusion (X : SSet.{u}) : cone X ⟶ suspension X :=
  pushout.inl _ _

/-- Inclusion of the upper cone. -/
abbrev upperConeInclusion (X : SSet.{u}) : cone X ⟶ suspension X :=
  pushout.inr _ _

/-- The two cone inclusions agree on their common equator. -/
theorem equator_glue (X : SSet.{u}) :
    bottomInclusion X ≫ lowerConeInclusion X =
      bottomInclusion X ≫ upperConeInclusion X :=
  pushout.condition

variable (P : X.Subcomplex)

/-- The copy of `P ⊗ Δ[1]` inside a cone. -/
def coneBaseLine : (P : SSet) ⊗ Δ[1] ⟶ cone X :=
  P.ι ▷ Δ[1] ≫ cylinderInclusion X

/-- The source pair inside a cone: its bottom together with the cone on
`P`. -/
abbrev conePairBoundary : (cone X).Subcomplex :=
  SSet.Subcomplex.range (bottomInclusion X) ⊔
    SSet.Subcomplex.range (coneBaseLine P)

variable (A : SimplicialObject AddCommGrpCat.{u})

/-- Precomposition as an additive homomorphism between mapping groups. -/
def precompHom (k : W ⟶ X) :
    (X ⟶ underlyingSSet A) →+ (W ⟶ underlyingSSet A) where
  toFun f := k ≫ f
  map_zero' := by ext Δ x; rfl
  map_add' _ _ := by ext Δ x; rfl

/-- Precomposition as a `ℤ`-linear map. -/
def precompLinear (k : W ⟶ X) :
    (X ⟶ underlyingSSet A) →ₗ[ℤ] (W ⟶ underlyingSSet A) :=
  (precompHom A k).toIntLinearMap

/-- Restriction of a suspension map to the lower copy of `P ⊗ Δ[1]`. -/
def lowerBaseLineRestriction :
    (suspension X ⟶ underlyingSSet A) →ₗ[ℤ]
      ((P : SSet) ⊗ Δ[1] ⟶ underlyingSSet A) :=
  precompLinear A (coneBaseLine P ≫ lowerConeInclusion X)

/-- Restriction of a suspension map to the upper copy of `P ⊗ Δ[1]`. -/
def upperBaseLineRestriction :
    (suspension X ⟶ underlyingSSet A) →ₗ[ℤ]
      ((P : SSet) ⊗ Δ[1] ⟶ underlyingSSet A) :=
  precompLinear A (coneBaseLine P ≫ upperConeInclusion X)

/-- Actual suspension maps which are zero on the basepoint cone in each
half. -/
abbrev PointedSuspensionMaps :
    Submodule ℤ (suspension X ⟶ underlyingSSet A) :=
  LinearMap.ker (lowerBaseLineRestriction P A) ⊓
    LinearMap.ker (upperBaseLineRestriction P A)

/-- Lower-cone-minus-upper-cone on actual suspension maps. -/
def coneDifferenceLinear :
    (suspension X ⟶ underlyingSSet A) →ₗ[ℤ]
      (cone X ⟶ underlyingSSet A) :=
  (precompLinear A (lowerConeInclusion X)) -
    (precompLinear A (upperConeInclusion X))

@[simp]
theorem coneDifferenceLinear_apply
    (F : suspension X ⟶ underlyingSSet A) :
    coneDifferenceLinear A F =
      lowerConeInclusion X ≫ F - upperConeInclusion X ≫ F :=
  rfl

/-- Precomposition distributes over the pointwise difference of maps. -/
theorem comp_subMap (k : W ⟶ X)
    (f g : X ⟶ underlyingSSet A) :
    k ≫ (f - g) = (k ≫ f) - (k ≫ g) := by
  rw [sub_eq_add_neg, comp_addMap, comp_negMap]
  exact (sub_eq_add_neg _ _).symm

/-- The two-cone difference vanishes on the common bottom. -/
theorem bottom_comp_coneDifference_eq_zero
    (F : suspension X ⟶ underlyingSSet A) :
    bottomInclusion X ≫ coneDifferenceLinear A F = 0 := by
  rw [coneDifferenceLinear_apply, comp_subMap]
  have h := equator_glue X
  have heval : bottomInclusion X ≫ lowerConeInclusion X ≫ F =
      bottomInclusion X ≫ upperConeInclusion X ≫ F := by
    rw [← Category.assoc, h, Category.assoc]
  rw [heval, sub_self]

/-- For a pointed suspension map, the two-cone difference also vanishes on
the copy of `P ⊗ Δ[1]`. -/
theorem baseLine_comp_coneDifference_eq_zero
    (F : PointedSuspensionMaps P A) :
    coneBaseLine P ≫ coneDifferenceLinear A F.1 = 0 := by
  rw [coneDifferenceLinear_apply, comp_subMap]
  have hlow : coneBaseLine P ≫ lowerConeInclusion X ≫ F.1 = 0 := by
    exact LinearMap.mem_ker.mp F.2.1
  have hupp : coneBaseLine P ≫ upperConeInclusion X ≫ F.1 = 0 := by
    exact LinearMap.mem_ker.mp F.2.2
  rw [hlow, hupp, sub_self]

/-- A pointed suspension map produces a strictly zero relative map on the
cone pair by lower-minus-upper. -/
def differenceRelativeZeroMap
    (F : PointedSuspensionMaps P A) :
    RelativeZeroMaps (conePairBoundary P) A := by
  refine ⟨coneDifferenceLinear A F.1, ?_⟩
  change (conePairBoundary P).ι ≫ coneDifferenceLinear A F.1 = 0
  ext Δ x
  rcases x.2 with hx | hx
  · rcases hx with ⟨y, hy⟩
    change (coneDifferenceLinear A F.1).app Δ x.1 = 0
    rw [← hy]
    have h := bottom_comp_coneDifference_eq_zero A F.1
    exact ConcreteCategory.congr_hom (congr_app h Δ) y
  · rcases hx with ⟨y, hy⟩
    change (coneDifferenceLinear A F.1).app Δ x.1 = 0
    rw [← hy]
    have h := baseLine_comp_coneDifference_eq_zero P A F
    exact ConcreteCategory.congr_hom (congr_app h Δ) y

/-- The relative two-cone difference is additive. -/
def differenceRelativeZeroHom :
    PointedSuspensionMaps P A →+
      RelativeZeroMaps (conePairBoundary P) A where
  toFun := differenceRelativeZeroMap P A
  map_zero' := by
    apply Subtype.ext
    change coneDifferenceLinear A
      (0 : suspension X ⟶ underlyingSSet A) = 0
    exact map_zero (coneDifferenceLinear A)
  map_add' F G := by
    apply Subtype.ext
    change coneDifferenceLinear A (F.1 + G.1) =
      coneDifferenceLinear A F.1 + coneDifferenceLinear A G.1
    exact map_add (coneDifferenceLinear A) F.1 G.1

/-- The relative two-cone difference as a `ℤ`-linear map. -/
def differenceRelativeZeroLinear :
    PointedSuspensionMaps P A →ₗ[ℤ]
      RelativeZeroMaps (conePairBoundary P) A :=
  (differenceRelativeZeroHom P A).toIntLinearMap

/-- The actual two-cone difference with target Mathlib's native relative
homotopy classes. -/
def twoConeDifferenceLinear :
    PointedSuspensionMaps P A →ₗ[ℤ]
      NativeHomotopyClass (conePairBoundary P) A :=
  (strictHomotopyClassLinear (conePairBoundary P) A).comp
    (differenceRelativeZeroLinear P A)

/-! ## Surjectivity -/

/-- A map which is strictly zero on a subcomplex is zero after
precomposition by any map whose range lies in that subcomplex. -/
theorem comp_eq_zero_of_range_le
    {Q : X.Subcomplex} (k : W ⟶ X)
    (hk : SSet.Subcomplex.range k ≤ Q)
    (f : RelativeZeroMaps Q A) :
    k ≫ f.1 = 0 := by
  let klift : W ⟶ (Q : SSet) := Q.lift k hk
  have hf : Q.ι ≫ f.1 = 0 := f.2
  calc
    k ≫ f.1 = (klift ≫ Q.ι) ≫ f.1 := by rw [Q.lift_ι]
    _ = klift ≫ (Q.ι ≫ f.1) := Category.assoc _ _ _
    _ = klift ≫ 0 := by rw [hf]
    _ = 0 := by ext Δ x; rfl

/-- Normalize a relative cone-pair map into a pointed suspension map by
placing it on the lower cone and zero on the upper cone. -/
def normalizedSuspensionMap
    (f : RelativeZeroMaps (conePairBoundary P) A) :
    PointedSuspensionMaps P A := by
  have hbottom : bottomInclusion X ≫ f.1 = 0 :=
    comp_eq_zero_of_range_le A (bottomInclusion X) le_sup_left f
  let F : suspension X ⟶ underlyingSSet A :=
    pushout.desc f.1 0 (by
      calc
        bottomInclusion X ≫ f.1 = 0 := hbottom
        _ = bottomInclusion X ≫ 0 := by ext Δ x; rfl)
  refine ⟨F, ?_, ?_⟩
  · change lowerBaseLineRestriction P A F = 0
    change coneBaseLine P ≫ lowerConeInclusion X ≫ F = 0
    rw [pushout.inl_desc]
    exact comp_eq_zero_of_range_le A (coneBaseLine P) le_sup_right f
  · change upperBaseLineRestriction P A F = 0
    change coneBaseLine P ≫ upperConeInclusion X ≫ F = 0
    rw [pushout.inr_desc]
    ext Δ x
    rfl

/-- The difference of the normalized lower-only suspension map is the
original relative cone-pair map. -/
theorem difference_normalizedSuspensionMap
    (f : RelativeZeroMaps (conePairBoundary P) A) :
    differenceRelativeZeroMap P A (normalizedSuspensionMap P A f) = f := by
  apply Subtype.ext
  change coneDifferenceLinear A
      (normalizedSuspensionMap P A f).1 = f.1
  rw [coneDifferenceLinear_apply]
  change lowerConeInclusion X ≫
      pushout.desc f.1 0 _ -
    upperConeInclusion X ≫ pushout.desc f.1 0 _ = f.1
  rw [pushout.inl_desc, pushout.inr_desc, sub_zero]

/-- The native two-cone difference is onto. -/
theorem twoConeDifferenceLinear_surjective :
    Function.Surjective (twoConeDifferenceLinear P A) := by
  intro c
  rcases c.eq_homotopyClass with ⟨r, rfl⟩
  let f : RelativeZeroMaps (conePairBoundary P) A :=
    (RelativeZeroMaps.equivRelativeMorphism
      (conePairBoundary P) A).symm r
  refine ⟨normalizedSuspensionMap P A f, ?_⟩
  change (RelativeZeroMaps.toRelativeMorphism (conePairBoundary P) A
      (differenceRelativeZeroMap P A
        (normalizedSuspensionMap P A f))).homotopyClass =
    r.homotopyClass
  rw [difference_normalizedSuspensionMap]
  change ((RelativeZeroMaps.equivRelativeMorphism
    (conePairBoundary P) A) f).homotopyClass = r.homotopyClass
  rw [(RelativeZeroMaps.equivRelativeMorphism
    (conePairBoundary P) A).apply_symm_apply]

/-- First-isomorphism-theorem form of the native two-cone difference. -/
def quotientTwoConeKernelEquiv :
    (PointedSuspensionMaps P A ⧸
      LinearMap.ker (twoConeDifferenceLinear P A)) ≃ₗ[ℤ]
      NativeHomotopyClass (conePairBoundary P) A :=
  (twoConeDifferenceLinear P A).quotKerEquivOfSurjective
    (twoConeDifferenceLinear_surjective P A)

@[simp]
theorem quotientTwoConeKernelEquiv_mkQ
    (F : PointedSuspensionMaps P A) :
    quotientTwoConeKernelEquiv P A
        ((LinearMap.ker (twoConeDifferenceLinear P A)).mkQ F) =
      twoConeDifferenceLinear P A F := by
  exact LinearMap.quotKerEquivOfSurjective_apply_mk
    (twoConeDifferenceLinear P A)
    (twoConeDifferenceLinear_surjective P A) F

end NativeDoubleCone
end GeneralSphereT.Section4
