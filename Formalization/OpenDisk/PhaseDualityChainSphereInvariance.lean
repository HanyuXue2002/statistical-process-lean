import Formalization.OpenDisk.PhaseDualityChainSphere

set_option linter.style.header false

/-!
# Classification from actual algebraic sphere data

This file accepts a concrete chain homotopy equivalence from a source chain
complex to the standard oriented sphere complex.  It proves, rather than
assumes, the resulting classification of actual chain homotopy classes.
The hypothesis is chain level data, not an equivalence with the desired
homology group.  No geometric triangulation comparison is asserted here.
-/

noncomputable section

open CategoryTheory HomologicalComplex

namespace OpenDisk.ChainClasses

universe u
variable {R : Type u} [CommRing R]
variable (C A : ChainComplex (ModuleCat.{u} R) ℕ)

/-- The submodule of chain maps equipped with an actual chain nullhomotopy. -/
def nullMaps : Submodule R (C ⟶ A) where
  carrier := {f | Nonempty (Homotopy f 0)}
  zero_mem' := ⟨Homotopy.refl 0⟩
  add_mem' := by
    rintro f g ⟨Hf⟩ ⟨Hg⟩
    exact ⟨by simpa using Hf.add Hg⟩
  smul_mem' := by
    rintro r f ⟨Hf⟩
    exact ⟨by simpa using Hf.smul r⟩

abbrev classes := (C ⟶ A) ⧸ nullMaps C A

theorem class_eq_iff {f g : C ⟶ A} :
    (Submodule.Quotient.mk f : classes C A) = Submodule.Quotient.mk g ↔
      Nonempty (Homotopy f g) := by
  rw [Submodule.Quotient.eq]
  exact Homotopy.equivSubZero.symm.nonempty_congr

variable {C A} {D : ChainComplex (ModuleCat.{u} R) ℕ}

def precompose (k : D ⟶ C) : (C ⟶ A) →ₗ[R] (D ⟶ A) where
  toFun f := k ≫ f
  map_add' f g := by simp only [Preadditive.comp_add]
  map_smul' r f := by simp only [Linear.comp_smul, RingHom.id_apply]

/-- Precomposition descends because actual chain homotopies compose. -/
def precomposeClasses (k : D ⟶ C) : classes C A →ₗ[R] classes D A :=
  (nullMaps C A).mapQ (nullMaps D A) (precompose k) (by
    rintro f ⟨H⟩
    exact ⟨by simpa [precompose] using H.compLeft k⟩)

@[simp]
theorem precomposeClasses_mk (k : D ⟶ C) (f : C ⟶ A) :
    precomposeClasses k (Submodule.Quotient.mk f) = Submodule.Quotient.mk (k ≫ f) := rfl

/-- Actual chain homotopy equivalences preserve the group of chain homotopy classes. -/
def equivOfHomotopyEquiv (e : HomotopyEquiv C D) : classes C A ≃ₗ[R] classes D A where
  toLinearMap := precomposeClasses e.inv
  invFun := precomposeClasses e.hom
  left_inv := by
    intro x
    obtain ⟨f, rfl⟩ := (nullMaps C A).mkQ_surjective x
    apply (class_eq_iff C A).mpr
    change Nonempty (Homotopy (e.hom ≫ (e.inv ≫ f)) f)
    exact ⟨by simpa only [Category.assoc] using e.homotopyHomInvId.compRightId f⟩
  right_inv := by
    intro x
    obtain ⟨f, rfl⟩ := (nullMaps D A).mkQ_surjective x
    apply (class_eq_iff D A).mpr
    change Nonempty (Homotopy (e.inv ≫ (e.hom ≫ f)) f)
    exact ⟨by simpa only [Category.assoc] using e.homotopyInvHomId.compRightId f⟩

/-- A concrete algebraic sphere source has the stated homology classification.
This is a theorem about actual chain maps and actual chain homotopies. -/
def equivHomologyOfSphere (n : ℕ) (e : HomotopyEquiv C (ChainSphere.sphere (R := R) n)) :
    classes C A ≃ₗ[R] A.homology n :=
  (equivOfHomotopyEquiv e).trans (ChainSphere.mapClassesEquivHomology A n)

end OpenDisk.ChainClasses
