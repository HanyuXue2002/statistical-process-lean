import Mathlib.Algebra.Exact.Basic
import Mathlib.LinearAlgebra.Isomorphisms

set_option linter.style.header false

/-!
# Section 4: quotient consequences of the exact rows

This file contains the choice-free quotient algebra used three times in
Section 4.  It deliberately does not know how mapping and relative homotopy
classes are constructed.  Once those standard topological objects are
presented as quotients by their null maps, the comparison isomorphisms are
forced by exactness.

Keeping this argument separate has two advantages: the representative
formulas are checked once, and the later simplicial-topology bridge cannot
silently change the algebra proved in Sections 2 and 3.
-/

noncomputable section

namespace GeneralSphereT.Section4

variable {A R M Q : Type*}
variable [AddCommGroup A] [AddCommGroup R] [AddCommGroup M] [AddCommGroup Q]

/-- An exact pair `R -> M -> Q`, with the second map onto, identifies `Q`
with the quotient of `M` by the image of the first map. -/
def targetEquivQuotientRange
    (ρ : R →ₗ[ℤ] M) (ω : M →ₗ[ℤ] Q)
    (hexact : Function.Exact ρ ω) (hω : Function.Surjective ω) :
    Q ≃ₗ[ℤ] M ⧸ LinearMap.range ρ :=
  (ω.quotKerEquivOfSurjective hω).symm.trans
    (Submodule.quotEquivOfEq (LinearMap.ker ω) (LinearMap.range ρ)
      (LinearMap.exact_iff.mp hexact))

/-- Representative formula for `targetEquivQuotientRange`: the class of
`ω(m)` is represented by `m`. -/
@[simp]
theorem targetEquivQuotientRange_apply
    (ρ : R →ₗ[ℤ] M) (ω : M →ₗ[ℤ] Q)
    (hexact : Function.Exact ρ ω) (hω : Function.Surjective ω) (m : M) :
    targetEquivQuotientRange ρ ω hexact hω (ω m) =
      (LinearMap.range ρ).mkQ m := by
  simp [targetEquivQuotientRange,
    LinearMap.quotKerEquivOfSurjective_symm_apply]

/-- If a separately defined subgroup `N` is known to be exactly the image
of `ρ`, the target is the quotient by `N`.  In Section 4, `N` is the subgroup
of pointed nullhomotopic maps. -/
def targetEquivQuotient
    (ρ : R →ₗ[ℤ] M) (ω : M →ₗ[ℤ] Q)
    (N : Submodule ℤ M)
    (hexact : Function.Exact ρ ω) (hω : Function.Surjective ω)
    (hN : LinearMap.range ρ = N) :
    Q ≃ₗ[ℤ] M ⧸ N :=
  (targetEquivQuotientRange ρ ω hexact hω).trans
    (Submodule.quotEquivOfEq (LinearMap.range ρ) N hN)

/-- Representative formula after replacing the image of `ρ` by a named
null-map subgroup. -/
@[simp]
theorem targetEquivQuotient_apply
    (ρ : R →ₗ[ℤ] M) (ω : M →ₗ[ℤ] Q)
    (N : Submodule ℤ M)
    (hexact : Function.Exact ρ ω) (hω : Function.Surjective ω)
    (hN : LinearMap.range ρ = N) (m : M) :
    targetEquivQuotient ρ ω N hexact hω hN (ω m) = N.mkQ m := by
  simp [targetEquivQuotient]

/-- First-isomorphism form used by the transgression: a surjective map whose
kernel is `B` descends to an isomorphism `Z/B -> Rel`. -/
def quotientEquivOfKer
    {Z Rel : Type*} [AddCommGroup Z] [AddCommGroup Rel]
    (B : Submodule ℤ Z) (tr : Z →ₗ[ℤ] Rel)
    (hker : LinearMap.ker tr = B) (htr : Function.Surjective tr) :
    (Z ⧸ B) ≃ₗ[ℤ] Rel :=
  (Submodule.quotEquivOfEq B (LinearMap.ker tr) hker.symm).trans
    (tr.quotKerEquivOfSurjective htr)

/-- The descended transgression keeps the expected representative. -/
@[simp]
theorem quotientEquivOfKer_apply
    {Z Rel : Type*} [AddCommGroup Z] [AddCommGroup Rel]
    (B : Submodule ℤ Z) (tr : Z →ₗ[ℤ] Rel)
    (hker : LinearMap.ker tr = B) (htr : Function.Surjective tr) (z : Z) :
    quotientEquivOfKer B tr hker htr (B.mkQ z) = tr z := by
  simp [quotientEquivOfKer]

/-- The suspension comparison is exactly the composition in (4.26):
transgression, inverse two-cone difference, and inverse degree-zero
comparison on the suspension. -/
def suspensionEquiv
    {TPrime Rel SuspMaps TauSusp : Type*}
    [AddCommGroup TPrime] [AddCommGroup Rel]
    [AddCommGroup SuspMaps] [AddCommGroup TauSusp]
    (tr : TPrime ≃ₗ[ℤ] Rel)
    (twoConeDifference : SuspMaps ≃ₗ[ℤ] Rel)
    (thetaSusp : TauSusp ≃ₗ[ℤ] SuspMaps) :
    TPrime ≃ₗ[ℤ] TauSusp :=
  (tr.trans twoConeDifference.symm).trans thetaSusp.symm

@[simp]
theorem suspensionEquiv_apply
    {TPrime Rel SuspMaps TauSusp : Type*}
    [AddCommGroup TPrime] [AddCommGroup Rel]
    [AddCommGroup SuspMaps] [AddCommGroup TauSusp]
    (tr : TPrime ≃ₗ[ℤ] Rel)
    (twoConeDifference : SuspMaps ≃ₗ[ℤ] Rel)
    (thetaSusp : TauSusp ≃ₗ[ℤ] SuspMaps) (x : TPrime) :
    suspensionEquiv tr twoConeDifference thetaSusp x =
      thetaSusp.symm (twoConeDifference.symm (tr x)) :=
  rfl

end GeneralSphereT.Section4
