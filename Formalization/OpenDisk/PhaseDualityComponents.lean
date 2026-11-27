import Formalization.OpenDisk.PhaseDualityTopology
import Mathlib.GroupTheory.FiniteAbelian.Basic
import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.LinearAlgebra.Finsupp.VectorSpace

set_option linter.style.header false

/-!
# Finitely many path components of finite integer-equation phase spaces

This uses the proved structure theorem for finitely generated abelian groups:
their circle-character spaces are continuous images of a torus times a finite
character group.  No compact-Lie-group theorem is assumed.
-/

noncomputable section

open scoped DirectSum

namespace OpenDisk.PhaseDuality

section PathComponents

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- A continuous surjection induces a surjection of genuine path components. -/
theorem finite_zerothHomotopy_of_surjective [Finite (ZerothHomotopy X)]
    (f : X → Y) (hf : Continuous f) (hs : Function.Surjective f) :
    Finite (ZerothHomotopy Y) := by
  let F : ZerothHomotopy X → ZerothHomotopy Y :=
    ZerothHomotopy.lift (fun x => ZerothHomotopy.mk (f x))
      (fun {_ _} p => ZerothHomotopy.sound (p.map hf))
  apply Finite.of_surjective F
  intro y
  obtain ⟨y, rfl⟩ := ZerothHomotopy.mk_surjective y
  obtain ⟨x, rfl⟩ := hs y
  exact ⟨ZerothHomotopy.mk x, rfl⟩

/-- A connected factor times a finite factor has finitely many path components. -/
theorem finite_zerothHomotopy_prod [PathConnectedSpace X] [Finite Y] :
    Finite (ZerothHomotopy (X × Y)) := by
  let x₀ : X := Classical.choice (PathConnectedSpace.nonempty (X := X))
  let f : Y → ZerothHomotopy (X × Y) := fun y => ZerothHomotopy.mk (x₀, y)
  apply Finite.of_surjective f
  intro z
  obtain ⟨⟨x, y⟩, rfl⟩ := ZerothHomotopy.mk_surjective z
  refine ⟨y, ?_⟩
  exact Quotient.sound ((PathConnectedSpace.joined x₀ x).prod (Joined.refl y))

end PathComponents

section Characters

variable {A T : Type*} [AddCommGroup A] [AddCommGroup T]

/-- A finite abelian group has only finitely many real-circle characters. -/
theorem finite_characterGroup [Finite T] : Finite (T →ₗ[ℤ] Phase) := by
  let f : (T →ₗ[ℤ] Phase) → AddChar T ℂ := fun χ =>
    AddChar.circleEquivComplex
      ((AddCircle.toCircle_addChar (T := 1)).compAddMonoidHom χ.toAddMonoidHom)
  apply Finite.of_injective f
  intro χ ψ h
  have hc := AddChar.circleEquivComplex.injective h
  ext t
  apply AddCircle.injective_toCircle one_ne_zero
  exact DFunLike.congr_fun hc t

/-- The dual of an explicit free-times-finite decomposition has finitely
many genuine path components. -/
theorem finite_character_components_of_decomposition [Finite T]
    (n : ℕ) (e : A ≃+ (Fin n →₀ ℤ) × T) :
    Finite (ZerothHomotopy (A →ₗ[ℤ] Phase)) := by
  letI : Finite (T →ₗ[ℤ] Phase) := finite_characterGroup
  letI : Finite (ZerothHomotopy ((Fin n → Phase) × (T →ₗ[ℤ] Phase))) :=
    finite_zerothHomotopy_prod
  let E : ((Fin n → Phase) × (T →ₗ[ℤ] Phase)) ≃ₗ[ℤ] (A →ₗ[ℤ] Phase) :=
    ((phaseTableEquiv (X := Fin n)).prodCongr (LinearEquiv.refl ℤ _)).trans
      ((LinearMap.coprodEquiv ℤ).trans
        (LinearEquiv.arrowCongr e.toIntLinearEquiv.symm (LinearEquiv.refl ℤ Phase)))
  have hE : Continuous E := by
    apply continuous_induced_rng.mpr
    apply continuous_pi
    intro a
    change Continuous (fun z : (Fin n → Phase) × (T →ₗ[ℤ] Phase) =>
      evaluate z.1 (e a).1 + z.2 (e a).2)
    exact ((continuous_evaluate_distribution (e a).1).comp continuous_fst).add
      ((continuous_character_evaluation (e a).2).comp continuous_snd)
  exact finite_zerothHomotopy_of_surjective E hE E.surjective

/-- General integer-equation component finiteness, derived from the actual
structure theorem for finitely generated abelian groups. -/
theorem finite_character_components [AddGroup.FG A] :
    Finite (ZerothHomotopy (A →ₗ[ℤ] Phase)) := by
  obtain ⟨n, ι, hι, p, hp, k, ⟨e⟩⟩ := AddCommGroup.equiv_free_prod_directSum_zmod A
  letI : Fintype ι := hι
  letI (i : ι) : NeZero (p i ^ k i) := ⟨pow_ne_zero (k i) (hp i).ne_zero⟩
  letI : Finite (⨁ i, ZMod (p i ^ k i)) :=
    Finite.of_equiv _ DFinsupp.equivFunOnFintype.symm
  exact finite_character_components_of_decomposition n e

end Characters

section IntegerEquations

variable {X : Type*} [Fintype X]

/-- Every collection of literal integer linear equations on a finite phase
table has finitely many path components.  The row subgroup is arbitrary;
finite generation of the ambient full distribution group is sufficient. -/
theorem finite_annihilator_components (J : Submodule ℤ (Distribution X)) :
    Finite (ZerothHomotopy (annihilator J)) := by
  letI : Module.Finite ℤ (Distribution X) := inferInstance
  letI : AddGroup.FG (Distribution X ⧸ J) := Module.Finite.iff_addGroup_fg.mp inferInstance
  letI : Finite (ZerothHomotopy ((Distribution X ⧸ J) →ₗ[ℤ] Phase)) :=
    finite_character_components
  let f : ((Distribution X ⧸ J) →ₗ[ℤ] Phase) → annihilator J := fun χ =>
    ⟨χ.comp J.mkQ, by
      intro x hx
      change χ (J.mkQ x) = 0
      have hz : J.mkQ x = 0 := (Submodule.Quotient.mk_eq_zero J).mpr hx
      rw [hz, map_zero]⟩
  have hf : Continuous f := by
    apply Continuous.subtype_mk
    apply continuous_induced_rng.mpr
    exact continuous_pi fun x => continuous_character_evaluation (J.mkQ x)
  have hs : Function.Surjective f := by
    intro χ
    refine ⟨J.liftQ χ.1 χ.2, ?_⟩
    apply Subtype.ext
    ext x
    rfl
  exact finite_zerothHomotopy_of_surjective f hf hs

variable {R : Type*}

/-- A literal family of integer rows acting on a full finite phase table. -/
def integerEquationPhases (rows : R → Distribution X) : Submodule ℤ (X → Phase) :=
  (annihilator (Submodule.span ℤ (Set.range rows))).comap phaseTableEquiv.toLinearMap

@[simp]
theorem mem_integerEquationPhases (rows : R → Distribution X) (φ : X → Phase) :
    φ ∈ integerEquationPhases rows ↔ ∀ r, evaluate φ (rows r) = 0 := by
  change Submodule.span ℤ (Set.range rows) ≤ LinearMap.ker (evaluate φ) ↔ _
  rw [Submodule.span_le]
  exact ⟨fun h r => h ⟨r, rfl⟩, fun h _ ⟨r, hr⟩ => hr ▸ h r⟩

/-- Finiteness of the actual path-component set of a full phase table cut
out by any family of integer rows. -/
theorem finite_integerEquationPhases_components (rows : R → Distribution X) :
    Finite (ZerothHomotopy (integerEquationPhases rows)) := by
  let J := Submodule.span ℤ (Set.range rows)
  letI : Finite (ZerothHomotopy (annihilator J)) := finite_annihilator_components J
  let e := (phaseTableEquiv (X := X)).ofSubmodule' (annihilator J)
  have he : Continuous e.symm := by
    apply Continuous.subtype_mk
    exact continuous_phaseTableEquiv_symm.comp continuous_subtype_val
  exact finite_zerothHomotopy_of_surjective e.symm he e.symm.surjective

end IntegerEquations

end OpenDisk.PhaseDuality
