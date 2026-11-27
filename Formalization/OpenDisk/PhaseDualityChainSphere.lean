import Mathlib.Algebra.Homology.Single
import Mathlib.Algebra.Homology.Homotopy
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Tactic

set_option linter.style.header false

/-!
# The standard sphere chain model

The reduced cellular chain complex of an oriented `n`-sphere is the complex
with one copy of the coefficient ring in degree `n`.  This file computes
maps from that *actual chain complex*, and their actual chain homotopies.
No arbitrary triangulation is assumed chain equivalent to this model.
-/

noncomputable section

open CategoryTheory HomologicalComplex

namespace OpenDisk.ChainSphere

universe u
variable {R : Type u} [CommRing R]

/-- The standard oriented sphere chain model, with its chosen generator. -/
abbrev sphere (n : ℕ) : ChainComplex (ModuleCat.{u} R) ℕ :=
  (single (ModuleCat R) (ComplexShape.down ℕ) n).obj (ModuleCat.of R R)

def generator (n : ℕ) : (sphere (R := R) n).X n :=
  (singleObjXSelf (ComplexShape.down ℕ) n (ModuleCat.of R R)).inv 1

variable (A : ChainComplex (ModuleCat.{u} R) ℕ) (n : ℕ)

/-- Ordinary cycles, including all degree-zero chains. -/
abbrev cycles := LinearMap.ker (A.d n (n - 1)).hom

/-- Evaluation of a chain map at the oriented generator. -/
def evaluation : (sphere (R := R) n ⟶ A) →ₗ[R] cycles A n where
  toFun f := ⟨f.f n (generator n), by
    have h := congrArg (fun k => k (generator (R := R) n)) (f.comm n (n - 1))
    change (A.d n (n - 1)).hom (f.f n (generator n)) = 0
    rw [single_obj_d, Limits.zero_comp] at h
    exact h⟩
  map_add' f g := by
    apply Subtype.ext
    rfl
  map_smul' r f := by
    apply Subtype.ext
    rfl

/-- A cycle determines the unique map from the standard sphere chain model. -/
def mapOfCycle (z : cycles A n) : sphere (R := R) n ⟶ A :=
  mkHomFromSingle (ModuleCat.ofHom (LinearMap.toSpanSingleton R (A.X n) z.1))
    (fun k hk => by
      have hk' : k = n - 1 := by
        simp only [ComplexShape.down_Rel] at hk
        omega
      subst k
      apply ModuleCat.hom_ext
      apply LinearMap.ext_ring
      simpa using z.2)

@[simp]
theorem evaluation_mapOfCycle (z : cycles A n) :
    evaluation A n (mapOfCycle A n z) = z := by
  apply Subtype.ext
  change (mapOfCycle A n z).f n (generator n) = z.1
  simp [mapOfCycle, generator, LinearMap.toSpanSingleton_apply_one]

theorem evaluation_injective : Function.Injective (evaluation A n) := by
  intro f g h
  apply from_single_hom_ext
  have h' := congrArg Subtype.val h
  apply (cancel_epi (singleObjXSelf (ComplexShape.down ℕ) n (ModuleCat.of R R)).inv).mp
  apply ModuleCat.hom_ext
  apply LinearMap.ext_ring
  exact h'

/-- Actual chain maps from `R[n]` are exactly degree-`n` cycles. -/
def mapsEquivCycles : (sphere (R := R) n ⟶ A) ≃ₗ[R] cycles A n :=
  LinearEquiv.ofBijective (evaluation A n)
    ⟨evaluation_injective A n, fun z => ⟨mapOfCycle A n z, evaluation_mapOfCycle A n z⟩⟩

/-- The ordinary boundary map, with codomain restricted to cycles. -/
abbrev boundary : A.X (n + 1) →ₗ[R] cycles A n :=
  (A.sc' (n + 1) n (n - 1)).moduleCatToCycles

/-- The standard concrete cycles-modulo-boundaries homology group. -/
abbrev homologyQuotient := cycles A n ⧸ LinearMap.range (boundary A n)

/-- The concrete quotient is isomorphic to Mathlib's categorical homology. -/
def homologyQuotientEquiv : homologyQuotient A n ≃ₗ[R] A.homology n :=
  (((A.sc' (n + 1) n (n - 1)).moduleCatLeftHomologyData.homologyIso).symm ≪≫
    (A.homologyIsoSc' (n + 1) n (n - 1) (by simp)
      (by cases n <;> simp [ChainComplex.next_nat_zero, ChainComplex.next_nat_succ])).symm).toLinearEquiv

/-- A chain homotopy changes the evaluated cycle by a boundary. -/
theorem evaluation_sub_of_homotopy {f g : sphere (R := R) n ⟶ A}
    (H : Homotopy f g) :
    evaluation A n f - evaluation A n g =
      boundary A n (H.hom n (n + 1) (generator n)) := by
  apply Subtype.ext
  have h := H.comm n
  rw [dNext_nat, single_obj_d, Limits.zero_comp, zero_add,
    prevD_eq H.hom (by simp : (ComplexShape.down ℕ).Rel (n + 1) n)] at h
  have h' := congrArg (fun k => k (generator (R := R) n)) h
  change f.f n (generator n) - g.f n (generator n) =
    (A.d (n + 1) n) (H.hom n (n + 1) (generator n))
  change f.f n (generator n) =
    (A.d (n + 1) n) (H.hom n (n + 1) (generator n)) + g.f n (generator n) at h'
  exact sub_eq_of_eq_add h'

/-- A primitive in degree `n+1` supplies the one nonzero component of a
chain nullhomotopy from the standard sphere source. -/
def primitiveHom (y : A.X (n + 1)) (i j : ℕ) :
    (sphere (R := R) n).X i ⟶ A.X j :=
  if hi : i = n then
    if hj : j = n + 1 then
      (singleObjXIsoOfEq (ComplexShape.down ℕ) n (ModuleCat.of R R) i hi).hom ≫
        ModuleCat.ofHom (LinearMap.toSpanSingleton R (A.X (n + 1)) y) ≫
          (A.XIsoOfEq hj).inv
    else 0
  else 0

theorem primitiveHom_zero (y : A.X (n + 1)) (i j : ℕ)
    (hij : ¬ (ComplexShape.down ℕ).Rel j i) : primitiveHom A n y i j = 0 := by
  unfold primitiveHom
  split_ifs with hi hj
  · subst i; subst j; simp at hij
  all_goals rfl

theorem evaluation_nullHomotopicMap (y : A.X (n + 1)) :
    evaluation A n (Homotopy.nullHomotopicMap (primitiveHom A n y)) = boundary A n y := by
  apply Subtype.ext
  change (dNext n (primitiveHom A n y) + prevD n (primitiveHom A n y)) (generator n) =
    (A.d (n + 1) n) y
  rw [dNext_nat, single_obj_d, Limits.zero_comp, zero_add,
    prevD_eq _ (by simp : (ComplexShape.down ℕ).Rel (n + 1) n)]
  simp [primitiveHom, generator, singleObjXSelf]

/-- The exact relation between actual chain nullhomotopy and ordinary boundaries. -/
theorem nullHomotopic_iff_boundary (f : sphere (R := R) n ⟶ A) :
    Nonempty (Homotopy f 0) ↔ evaluation A n f ∈ LinearMap.range (boundary A n) := by
  constructor
  · rintro ⟨H⟩
    refine ⟨H.hom n (n + 1) (generator n), ?_⟩
    simpa using (evaluation_sub_of_homotopy A n H).symm
  · rintro ⟨y, hy⟩
    have he : Homotopy.nullHomotopicMap (primitiveHom A n y) = f :=
      evaluation_injective A n ((evaluation_nullHomotopicMap A n y).trans hy)
    rw [← he]
    exact ⟨Homotopy.nullHomotopy (primitiveHom A n y) (primitiveHom_zero A n y)⟩

/-- The submodule of genuinely chain-nullhomotopic maps. -/
def nullMaps : Submodule R (sphere (R := R) n ⟶ A) where
  carrier := {f | Nonempty (Homotopy f 0)}
  zero_mem' := ⟨Homotopy.refl 0⟩
  add_mem' := by
    rintro f g ⟨Hf⟩ ⟨Hg⟩
    exact ⟨by simpa using Hf.add Hg⟩
  smul_mem' := by
    rintro r f ⟨Hf⟩
    exact ⟨by simpa using Hf.smul r⟩

/-- Chain-homotopy classes of maps from the standard sphere model. -/
abbrev mapClasses := (sphere (R := R) n ⟶ A) ⧸ nullMaps A n

def evaluationHomology : (sphere (R := R) n ⟶ A) →ₗ[R] homologyQuotient A n :=
  (LinearMap.range (boundary A n)).mkQ.comp (evaluation A n)

theorem evaluationHomology_surjective : Function.Surjective (evaluationHomology A n) :=
  (LinearMap.range (boundary A n)).mkQ_surjective.comp (mapsEquivCycles A n).surjective

theorem ker_evaluationHomology : LinearMap.ker (evaluationHomology A n) = nullMaps A n := by
  ext f
  change evaluationHomology A n f = 0 ↔ Nonempty (Homotopy f 0)
  rw [nullHomotopic_iff_boundary]
  exact Submodule.Quotient.mk_eq_zero _

/-- Evaluation on the oriented generator identifies actual chain-homotopy
classes from `R[n]` with the actual degree-`n` homology object. -/
def mapClassesEquivHomology : mapClasses A n ≃ₗ[R] A.homology n :=
  (Submodule.quotEquivOfEq (nullMaps A n) (LinearMap.ker (evaluationHomology A n))
    (ker_evaluationHomology A n).symm).trans
      ((LinearMap.quotKerEquivOfSurjective (evaluationHomology A n)
        (evaluationHomology_surjective A n)).trans (homologyQuotientEquiv A n))

end OpenDisk.ChainSphere
