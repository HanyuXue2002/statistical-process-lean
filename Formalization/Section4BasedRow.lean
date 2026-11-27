import Formalization.Section4ExactConsequences

set_option linter.style.header false

/-!
# Section 4: passing an exact restriction row to based objects

The passage from (4.1) to (4.3) is elementary but easy to leave implicit.
This file checks it once in a form that covers both cases in the paper.  An
evaluation at the basepoint is given on primitive relations and on strict
sections, restriction commutes with evaluation, cycles already vanish at the
basepoint, and constant relations split evaluation.  Subtracting the constant
value then proves surjectivity of the based obstruction map.
-/

noncomputable section

namespace GeneralSphereT.Section4

universe uZ uR uM uQ uA

variable {Z : Type uZ} {R : Type uR} {M : Type uM}
variable {Q : Type uQ} {A : Type uA}
variable [AddCommGroup Z] [AddCommGroup R] [AddCommGroup M]
variable [AddCommGroup Q] [AddCommGroup A]

/-- The basepoint-evaluation data used to normalize the degree-zero row.

For `q = 1`, `constantLift` is the global-constant lift described after
(4.4).  For `q > 1`, the evaluation group is zero and all fields are
automatic. -/
structure BasedRowData
    (A : Type uA) [AddCommGroup A]
    (i : Z →ₗ[ℤ] R) (ρ : R →ₗ[ℤ] M) where
  evalR : R →ₗ[ℤ] A
  evalM : M →ₗ[ℤ] A
  eval_restriction : evalM.comp ρ = evalR
  cycles_based : evalR.comp i = 0
  constantLift : A →ₗ[ℤ] R
  eval_constantLift : evalR.comp constantLift = LinearMap.id

namespace BasedRowData

variable {i : Z →ₗ[ℤ] R} {ρ : R →ₗ[ℤ] M}
variable (B : BasedRowData A i ρ)

/-- Primitive relations vanishing at the basepoint. -/
abbrev BasedRelations := LinearMap.ker B.evalR

/-- Strict sections vanishing at the basepoint. -/
abbrev BasedSections := LinearMap.ker B.evalM

/-- Cycles land in based primitive relations. -/
def cyclesToBasedRelations : Z →ₗ[ℤ] B.BasedRelations :=
  LinearMap.codRestrict B.BasedRelations i fun z => by
    rw [LinearMap.mem_ker]
    have h := LinearMap.congr_fun B.cycles_based z
    simpa using h

@[simp]
theorem cyclesToBasedRelations_coe (z : Z) :
    (B.cyclesToBasedRelations z : R) = i z :=
  rfl

/-- Restriction preserves the basepoint-zero condition. -/
def basedRestriction : B.BasedRelations →ₗ[ℤ] B.BasedSections :=
  LinearMap.codRestrict B.BasedSections
    (ρ.comp B.BasedRelations.subtype) fun r => by
      rw [LinearMap.mem_ker]
      have h := LinearMap.congr_fun B.eval_restriction r.1
      simpa [r.2] using h

@[simp]
theorem basedRestriction_coe (r : B.BasedRelations) :
    (B.basedRestriction r : M) = ρ r :=
  rfl

/-- Restrict the obstruction map to based sections. -/
def basedObstruction (ω : M →ₗ[ℤ] Q) : B.BasedSections →ₗ[ℤ] Q :=
  ω.comp B.BasedSections.subtype

@[simp]
theorem basedObstruction_apply (ω : M →ₗ[ℤ] Q)
    (m : B.BasedSections) :
    B.basedObstruction ω m = ω m :=
  rfl

/-- Injectivity at the left end survives passage to based objects. -/
theorem cyclesToBasedRelations_injective
    (hi : Function.Injective i) :
    Function.Injective B.cyclesToBasedRelations := by
  intro x y hxy
  apply hi
  exact congrArg Subtype.val hxy

/-- Exactness at primitive relations survives passage to kernels of
basepoint evaluation. -/
theorem exact_cyclesToBasedRelations_basedRestriction
    (hexact : Function.Exact i ρ) :
    Function.Exact B.cyclesToBasedRelations B.basedRestriction := by
  intro r
  constructor
  · intro hr
    have hrho : ρ (r : R) = 0 := congrArg Subtype.val hr
    rcases (hexact (r : R)).mp hrho with ⟨z, hz⟩
    refine ⟨z, ?_⟩
    apply Subtype.ext
    exact hz
  · rintro ⟨z, rfl⟩
    apply Subtype.ext
    exact (hexact (i z)).mpr ⟨z, rfl⟩

/-- Exactness at strict sections survives passage to based objects. -/
theorem exact_basedRestriction_basedObstruction
    (ω : M →ₗ[ℤ] Q) (hexact : Function.Exact ρ ω) :
    Function.Exact B.basedRestriction (B.basedObstruction ω) := by
  intro m
  constructor
  · intro hm
    have hω : ω (m : M) = 0 := hm
    rcases (hexact (m : M)).mp hω with ⟨r, hr⟩
    have hrBased : B.evalR r = 0 := by
      have heval := LinearMap.congr_fun B.eval_restriction r
      calc
        B.evalR r = B.evalM (ρ r) := by simpa using heval.symm
        _ = B.evalM m := by rw [hr]
        _ = 0 := m.2
    refine ⟨⟨r, hrBased⟩, ?_⟩
    apply Subtype.ext
    exact hr
  · rintro ⟨r, rfl⟩
    change ω (ρ (r : R)) = 0
    have hcomp := LinearMap.congr_fun hexact.linearMap_comp_eq_zero (r : R)
    simpa using hcomp

/-- Every obstruction class has a based representative: subtract the
constant lift of its basepoint value. -/
theorem basedObstruction_surjective
    (ω : M →ₗ[ℤ] Q) (hexact : Function.Exact ρ ω)
    (hω : Function.Surjective ω) :
    Function.Surjective (B.basedObstruction ω) := by
  intro q
  rcases hω q with ⟨m, hm⟩
  let r₀ : R := B.constantLift (B.evalM m)
  let m₀ : M := m - ρ r₀
  have hm₀ : B.evalM m₀ = 0 := by
    change B.evalM (m - ρ r₀) = 0
    rw [map_sub]
    have heval : B.evalM (ρ r₀) = B.evalR r₀ :=
      LinearMap.congr_fun B.eval_restriction r₀
    rw [heval]
    change B.evalM m - B.evalR (B.constantLift (B.evalM m)) = 0
    have hconst := LinearMap.congr_fun B.eval_constantLift (B.evalM m)
    exact sub_eq_zero.mpr (by simpa using hconst.symm)
  refine ⟨⟨m₀, hm₀⟩, ?_⟩
  change ω m₀ = q
  change ω (m - ρ r₀) = q
  rw [map_sub]
  have hzero := LinearMap.congr_fun hexact.linearMap_comp_eq_zero r₀
  rw [show ω (ρ r₀) = 0 by simpa using hzero, sub_zero, hm]

end BasedRowData

end GeneralSphereT.Section4
