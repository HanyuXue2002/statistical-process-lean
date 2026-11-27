import Formalization.Section4RelativeMappingGroups
import Formalization.Section4ReducedFreeFiber

set_option linter.style.header false

/-!
# Section 4: maps into the actual fibre

The fibre `F(G,q)` is a kernel in simplicial abelian groups.  This file
records the corresponding universal property at the level of genuine
simplicial-set maps: maps into `F` are exactly maps into
`reducedFree L(G,q)` whose composite with `d_*` is zero.  The equivalence is
additive and uses the degreewise kernel identification already proved in
`Section4ReducedFreeFiber`.
-/

noncomputable section

open CategoryTheory CategoryTheory.Category Opposite Simplicial

namespace GeneralSphereT.Section4

open GeneralSphereT.StandardModels
open UnderlyingSSet

universe u

variable (X : SSet.{u}) (G : AddCommGrpCat.{u}) (q : ℕ)

/-- The underlying simplicial-set map induced by a morphism of simplicial
abelian groups. -/
abbrev underlyingMap {A B : SimplicialObject AddCommGrpCat.{u}}
    (f : A ⟶ B) : underlyingSSet A ⟶ underlyingSSet B :=
  Functor.whiskerRight f (forget AddCommGrpCat.{u})

/-- Postcomposition by the reduced-free coboundary. -/
def postcomposeReducedFreeD :
    (X ⟶ underlyingSSet (reducedFree (L G q))) →+
      (X ⟶ underlyingSSet (reducedFree (K G q))) where
  toFun f := f ≫ underlyingMap (reducedFreeMap (d G q))
  map_zero' := by
    ext Δ x
    rfl
  map_add' f g := by
    ext Δ x
    change
      (reducedFreeMap (d G q)).app Δ
          (f.app Δ x + g.app Δ x) =
        (reducedFreeMap (d G q)).app Δ (f.app Δ x) +
          (reducedFreeMap (d G q)).app Δ (g.app Δ x)
    exact map_add ((reducedFreeMap (d G q)).app Δ).hom _ _

/-- Actual maps into `reducedFree L` which are killed by `d_*`. -/
abbrev MapsKilledByD :=
  AddMonoidHom.ker (postcomposeReducedFreeD X G q)

namespace MapsKilledByD

/-- The pointwise kernel membership carried by a map killed by `d_*`. -/
theorem app_mem (f : MapsKilledByD X G q)
    (Δ : SimplexCategoryᵒᵖ) (x : X.obj Δ) :
    (reducedFreeMap (d G q)).app Δ (f.1.app Δ x) = 0 := by
  have h := AddMonoidHom.mem_ker.mp f.2
  have hΔ := congr_app h Δ
  exact ConcreteCategory.congr_hom hΔ x

/-- Factor a map killed by `d_*` through the actual simplicial kernel. -/
def toFiberMap (f : MapsKilledByD X G q) :
    X ⟶ underlyingSSet (F G q) where
  app Δ := ↾fun x ↦
    FDegreeMk G q Δ (f.1.app Δ x) (app_mem X G q f Δ x)
  naturality Δ Δ' θ := by
    ext x
    apply (AddCommGrpCat.mono_iff_injective ((Fι G q).app Δ')).mp
      (inferInstance : Mono ((Fι G q).app Δ'))
    let z := FDegreeMk G q Δ (f.1.app Δ x) (app_mem X G q f Δ x)
    have hι := ConcreteCategory.congr_hom ((Fι G q).naturality θ)
      z
    change
      (Fι G q).app Δ' ((F G q).map θ z) =
        (reducedFree (L G q)).map θ ((Fι G q).app Δ z) at hι
    dsimp [z] at hι
    rw [FDegreeMk_inclusion] at hι
    change
      (Fι G q).app Δ'
          (FDegreeMk G q Δ' (f.1.app Δ' (X.map θ x)) _) =
        (Fι G q).app Δ' ((F G q).map θ z)
    rw [FDegreeMk_inclusion, hι]
    exact ConcreteCategory.congr_hom (f.1.naturality θ) x

/-- Compose a genuine map to `F` with the kernel inclusion. -/
def ofFiberMap (f : X ⟶ underlyingSSet (F G q)) :
    MapsKilledByD X G q := by
  refine ⟨f ≫ underlyingMap (Fι G q), AddMonoidHom.mem_ker.mpr ?_⟩
  change
    f ≫ underlyingMap (Fι G q) ≫
        underlyingMap (reducedFreeMap (d G q)) = 0
  ext Δ x
  have h := ConcreteCategory.congr_hom
    (NatTrans.congr_app (F_condition G q) Δ) (f.app Δ x)
  exact h

@[simp]
theorem toFiberMap_comp_inclusion (f : MapsKilledByD X G q) :
    toFiberMap X G q f ≫ underlyingMap (Fι G q) = f.1 := by
  ext Δ x
  exact FDegreeMk_inclusion G q Δ _ _

@[simp]
theorem ofFiberMap_coe (f : X ⟶ underlyingSSet (F G q)) :
    (ofFiberMap X G q f : X ⟶ underlyingSSet (reducedFree (L G q))) =
      f ≫ underlyingMap (Fι G q) :=
  rfl

/-- Maps into the categorical fibre are literally maps killed by the
reduced-free coboundary. -/
def equivFiberMaps :
    MapsKilledByD X G q ≃ (X ⟶ underlyingSSet (F G q)) where
  toFun := toFiberMap X G q
  invFun := ofFiberMap X G q
  left_inv f := by
    apply Subtype.ext
    exact toFiberMap_comp_inclusion X G q f
  right_inv f := by
    ext Δ x
    apply (AddCommGrpCat.mono_iff_injective ((Fι G q).app Δ)).mp
      (inferInstance : Mono ((Fι G q).app Δ))
    change
      (Fι G q).app Δ
          (FDegreeMk G q Δ
            ((ofFiberMap X G q f).1.app Δ x)
            (app_mem X G q (ofFiberMap X G q f) Δ x)) =
        (Fι G q).app Δ (f.app Δ x)
    rw [FDegreeMk_inclusion]
    rfl

/-- The kernel factorization is additive. -/
def addEquivFiberMaps :
    MapsKilledByD X G q ≃+
      (X ⟶ underlyingSSet (F G q)) where
  __ := equivFiberMaps X G q
  map_add' f g := by
    ext Δ x
    apply (AddCommGrpCat.mono_iff_injective ((Fι G q).app Δ)).mp
      (inferInstance : Mono ((Fι G q).app Δ))
    change
      (Fι G q).app Δ
          (FDegreeMk G q Δ ((f + g).1.app Δ x)
            (app_mem X G q (f + g) Δ x)) =
        (Fι G q).app Δ
          (FDegreeMk G q Δ (f.1.app Δ x) (app_mem X G q f Δ x) +
            FDegreeMk G q Δ (g.1.app Δ x) (app_mem X G q g Δ x))
    rw [FDegreeMk_inclusion, map_add, FDegreeMk_inclusion,
      FDegreeMk_inclusion]
    rfl

end MapsKilledByD

/-! ## Relative and pointed maps -/

open RelativeMapping

variable (P : X.Subcomplex)

/-- Restrict a map killed by `d_*` to a source subcomplex. -/
def restrictKilledByD :
    MapsKilledByD X G q →+
      ((P : SSet) ⟶ underlyingSSet (reducedFree (L G q))) where
  toFun f := P.ι ≫ f.1
  map_zero' := by
    ext Δ x
    rfl
  map_add' f g := by
    ext Δ x
    rfl

/-- Maps to `reducedFree L` which both vanish on `P` and are killed by
`d_*`. -/
abbrev RelativeMapsKilledByD :=
  AddMonoidHom.ker (restrictKilledByD X G q P)

namespace RelativeMapsKilledByD

/-- Factor a strictly relative map killed by `d_*` through the actual
fibre. -/
def toRelativeFiberMap (f : RelativeMapsKilledByD X G q P) :
    RelativeZeroMaps P (F G q) := by
  refine ⟨MapsKilledByD.toFiberMap X G q f.1,
    AddMonoidHom.mem_ker.mpr ?_⟩
  change P.ι ≫ MapsKilledByD.toFiberMap X G q f.1 = 0
  ext Δ x
  apply (AddCommGrpCat.mono_iff_injective ((Fι G q).app Δ)).mp
    (inferInstance : Mono ((Fι G q).app Δ))
  change
    (Fι G q).app Δ
        (FDegreeMk G q Δ (f.1.1.app Δ (P.ι.app Δ x)) _) =
      (Fι G q).app Δ 0
  rw [FDegreeMk_inclusion, map_zero]
  have h := AddMonoidHom.mem_ker.mp f.2
  exact ConcreteCategory.congr_hom (congr_app h Δ) x

/-- Forget a relative fibre map to its composite with the kernel
inclusion. -/
def ofRelativeFiberMap (f : RelativeZeroMaps P (F G q)) :
    RelativeMapsKilledByD X G q P := by
  refine ⟨MapsKilledByD.ofFiberMap X G q f.1,
    AddMonoidHom.mem_ker.mpr ?_⟩
  change P.ι ≫ f.1 ≫ underlyingMap (Fι G q) = 0
  rw [← Category.assoc]
  have hf := AddMonoidHom.mem_ker.mp f.2
  change P.ι ≫ f.1 = 0 at hf
  rw [hf]
  ext Δ x
  change (Fι G q).app Δ 0 = 0
  exact map_zero ((Fι G q).app Δ).hom

/-- The kernel universal property with a strict source boundary condition. -/
def addEquivRelativeFiberMaps :
    RelativeMapsKilledByD X G q P ≃+
      RelativeZeroMaps P (F G q) where
  toFun := toRelativeFiberMap X G q P
  invFun := ofRelativeFiberMap X G q P
  left_inv f := by
    apply Subtype.ext
    apply Subtype.ext
    exact MapsKilledByD.toFiberMap_comp_inclusion X G q f.1
  right_inv f := by
    apply Subtype.ext
    exact (MapsKilledByD.equivFiberMaps X G q).right_inv f.1
  map_add' f g := by
    apply Subtype.ext
    exact (MapsKilledByD.addEquivFiberMaps X G q).map_add f.1 g.1

/-- Native relative-morphism form of the same equivalence. -/
def addEquivNativeRelativeFiberMaps :
    RelativeMapsKilledByD X G q P ≃+
      SSet.RelativeMorphism P (zeroSubcomplex (F G q))
        (zeroBoundary P (F G q)) :=
  (addEquivRelativeFiberMaps X G q P).trans
    (relativeMorphismAddEquiv P (F G q))

end RelativeMapsKilledByD

end GeneralSphereT.Section4
