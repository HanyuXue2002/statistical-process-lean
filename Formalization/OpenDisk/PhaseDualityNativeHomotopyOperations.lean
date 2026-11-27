import Formalization.OpenDisk.PhaseDualityNativeChainHomotopy
import Formalization.Section4DoldKanDiskNativeContraction

set_option linter.style.header false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory CategoryTheory.Category Opposite Simplicial
open GeneralSphereT.Section4 GeneralSphereT.Section4.UnderlyingSSet
open GeneralSphereT.Section4.NativeRelativeHomotopyGroup
open GeneralSphereT.Section4.SimplicialObjectCylinderHomotopy
open scoped BigOperators

namespace OpenDisk.NativeHomotopies

universe u
variable {X Y Z : SSet.{u}} {A B : SimplicialObject AddCommGrpCat.{u}}

def precomp {f g : Y ⟶ Z} (H : SSet.Homotopy f g) (p : X ⟶ Y) :
    SSet.Homotopy (p ≫ f) (p ≫ g) :=
  toCylinderHomotopy (H.toSimplicialObjectHomotopy.precomp p)

def postcomp {f g : X ⟶ Y} (H : SSet.Homotopy f g) (p : Y ⟶ Z) :
    SSet.Homotopy (f ≫ p) (g ≫ p) :=
  toCylinderHomotopy (H.toSimplicialObjectHomotopy.postcomp p)

@[simp]
theorem comp_zero (p : X ⟶ Y) : p ≫ (0 : Y ⟶ underlyingSSet A) = 0 := by
  ext Δ x
  rfl

@[simp]
theorem zero_comp (p : A ⟶ B) :
    (0 : X ⟶ underlyingSSet A) ≫ Functor.whiskerRight p (forget AddCommGrpCat) = 0 := by
  ext Δ x
  exact map_zero (p.app Δ).hom

def zero : SSet.Homotopy (0 : X ⟶ underlyingSSet A) 0 :=
  toCylinderHomotopy (SimplicialObject.Homotopy.refl 0)

/-- Add actual cylinder homotopies into a simplicial abelian target. -/
def add {f g : X ⟶ underlyingSSet A}
    (H : SSet.Homotopy 0 f) (K : SSet.Homotopy 0 g) :
    SSet.Homotopy 0 (f + g) where
  h := H.h + K.h
  h₀ := by
    rw [comp_addMap, H.h₀, K.h₀]
    exact zero_add _
  h₁ := by rw [comp_addMap, H.h₁, K.h₁]; rfl
  rel := by
    ext Δ x
    exact False.elim x.1.2

theorem sum {ι : Type*} (s : Finset ι) (f : ι → (X ⟶ underlyingSSet A))
    (h : ∀ i ∈ s, Nonempty (SSet.Homotopy 0 (f i))) :
    Nonempty (SSet.Homotopy 0 (∑ i ∈ s, f i)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (show Nonempty (SSet.Homotopy (0 : X ⟶ underlyingSSet A) 0) from ⟨zero⟩)
  | @insert i s hi ih =>
      obtain ⟨H⟩ := h i (Finset.mem_insert_self _ _)
      obtain ⟨K⟩ := ih (fun j hj => h j (Finset.mem_insert_of_mem hj))
      simpa only [Finset.sum_insert hi] using (show Nonempty (SSet.Homotopy 0 (f i + ∑ j ∈ s, f j))
        from ⟨add H K⟩)

def postcompNull {f : X ⟶ underlyingSSet A} (H : SSet.Homotopy 0 f) (p : A ⟶ B) :
    SSet.Homotopy 0 (f ≫ Functor.whiskerRight p (forget AddCommGrpCat)) := by
  simpa only [zero_comp] using postcomp H (Functor.whiskerRight p (forget AddCommGrpCat))

def precompNull {f : Y ⟶ underlyingSSet A} (H : SSet.Homotopy 0 f) (p : X ⟶ Y) :
    SSet.Homotopy 0 (p ≫ f) := by
  simpa only [comp_zero] using precomp H p

end OpenDisk.NativeHomotopies
