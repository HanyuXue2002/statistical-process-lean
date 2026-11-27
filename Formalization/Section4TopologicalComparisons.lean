import Formalization.Section4BasedRow
import Formalization.PrimitiveQuotient

set_option linter.style.header false

/-!
# Section 4: mapping-class, transgression, and suspension comparisons

Mathlib does not yet provide a simplicial homotopy-group API that directly
turns maps of finite simplicial complexes into additive pointed homotopy
classes.  We therefore keep that standard topological layer explicit: a
pointed mapping group is presented by its subgroup of nullhomotopic maps, and
a relative mapping group is supplied together with the extension-class map.

All quotient algebra in Propositions 4.3 and 4.5 and in (4.26)--(4.27) is
proved here.  The hypotheses left visible are exactly the geometric claims:
the cone criterion identifies null maps with restrictions of primitive
relations; relative uniqueness identifies the kernel of the extension-class
map; and pointed cofiber exactness supplies the two-cone difference.
-/

noncomputable section

namespace GeneralSphereT.Section4

universe uZ uR uM uQ uA uRel uLoop

variable {Z : Type uZ} {R : Type uR} {M : Type uM}
variable {Q : Type uQ} {A : Type uA}
variable [AddCommGroup Z] [AddCommGroup R] [AddCommGroup M]
variable [AddCommGroup Q] [AddCommGroup A]

/-- Pointed homotopy classes, presented as pointed maps modulo the subgroup
of pointed nullhomotopic maps. -/
abbrev PointedHomotopyClasses
    (Maps : Type*) [AddCommGroup Maps] (NullMaps : Submodule ℤ Maps) :=
  Maps ⧸ NullMaps

section DegreeZeroComparison

variable {i : Z →ₗ[ℤ] R} {ρ : R →ₗ[ℤ] M} {ω : M →ₗ[ℤ] Q}
variable (B : BasedRowData A i ρ)

/-- Proposition 4.3, once the pointed cone criterion has identified the image
of primitive restriction with the nullhomotopic maps. -/
def theta
    (NullMaps : Submodule ℤ B.BasedSections)
    (hexact : Function.Exact ρ ω)
    (hω : Function.Surjective ω)
    (hnull : LinearMap.range B.basedRestriction = NullMaps) :
    Q ≃ₗ[ℤ] PointedHomotopyClasses B.BasedSections NullMaps :=
  targetEquivQuotient B.basedRestriction (B.basedObstruction ω)
    NullMaps
    (B.exact_basedRestriction_basedObstruction ω hexact)
    (B.basedObstruction_surjective ω hexact hω)
    hnull

/-- Formula (4.14): the obstruction of a based lift is represented by the
corresponding pointed section. -/
@[simp]
theorem theta_obstruction
    (NullMaps : Submodule ℤ B.BasedSections)
    (hexact : Function.Exact ρ ω)
    (hω : Function.Surjective ω)
    (hnull : LinearMap.range B.basedRestriction = NullMaps)
    (m : B.BasedSections) :
    theta B NullMaps hexact hω hnull (B.basedObstruction ω m) =
      NullMaps.mkQ m := by
  exact targetEquivQuotient_apply B.basedRestriction
    (B.basedObstruction ω) NullMaps
    (B.exact_basedRestriction_basedObstruction ω hexact)
    (B.basedObstruction_surjective ω hexact hω) hnull m

end DegreeZeroComparison

section Transgression

variable {Rel : Type uRel} [AddCommGroup Rel]

/-- Proposition 4.5: after relative extension has produced an additive class
map on cycles, relative uniqueness and the two cone arguments say precisely
that its kernel is `B` and that it is onto. -/
def transgression
    (B : Submodule ℤ Z) (extensionClass : Z →ₗ[ℤ] Rel)
    (hker : LinearMap.ker extensionClass = B)
    (hsurj : Function.Surjective extensionClass) :
    (Z ⧸ B) ≃ₗ[ℤ] Rel :=
  quotientEquivOfKer B extensionClass hker hsurj

/-- Representative formula (4.18). -/
@[simp]
theorem transgression_mkQ
    (B : Submodule ℤ Z) (extensionClass : Z →ₗ[ℤ] Rel)
    (hker : LinearMap.ker extensionClass = B)
    (hsurj : Function.Surjective extensionClass) (z : Z) :
    transgression B extensionClass hker hsurj (B.mkQ z) =
      extensionClass z :=
  quotientEquivOfKer_apply B extensionClass hker hsurj z

/-- Formula (4.24), with the standard loop--suspension adjunction kept as
the explicit second equivalence. -/
def loopSuspensionComparison
    {LoopMaps : Type uLoop} [AddCommGroup LoopMaps]
    (B : Submodule ℤ Z) (extensionClass : Z →ₗ[ℤ] Rel)
    (hker : LinearMap.ker extensionClass = B)
    (hsurj : Function.Surjective extensionClass)
    (relativeLoopAdjunction : Rel ≃ₗ[ℤ] LoopMaps) :
    (Z ⧸ B) ≃ₗ[ℤ] LoopMaps :=
  (transgression B extensionClass hker hsurj).trans
    relativeLoopAdjunction

end Transgression

section Suspension

variable {TPrime Rel SuspMaps TauSusp : Type*}
variable [AddCommGroup TPrime] [AddCommGroup Rel]
variable [AddCommGroup SuspMaps] [AddCommGroup TauSusp]

/-- Theorem (4.26), now as the literal composition stated in the paper.
The inputs are Proposition 4.5, pointed two-cone difference (4.25), and
Proposition 4.3 on the suspension. -/
def suspensionComparison
    (tr : TPrime ≃ₗ[ℤ] Rel)
    (twoConeDifference : SuspMaps ≃ₗ[ℤ] Rel)
    (thetaSusp : TauSusp ≃ₗ[ℤ] SuspMaps) :
    TPrime ≃ₗ[ℤ] TauSusp :=
  suspensionEquiv tr twoConeDifference thetaSusp

@[simp]
theorem suspensionComparison_apply
    (tr : TPrime ≃ₗ[ℤ] Rel)
    (twoConeDifference : SuspMaps ≃ₗ[ℤ] Rel)
    (thetaSusp : TauSusp ≃ₗ[ℤ] SuspMaps) (x : TPrime) :
    suspensionComparison tr twoConeDifference thetaSusp x =
      thetaSusp.symm (twoConeDifference.symm (tr x)) :=
  rfl

end Suspension

section SphereCorollary

variable {TauX MapsXF PiDF Hnext : Type*}
variable {TPrimeX MapsXLoopF PiDLoopF HnextNext : Type*}
variable [AddCommGroup TauX] [AddCommGroup MapsXF]
variable [AddCommGroup PiDF] [AddCommGroup Hnext]
variable [AddCommGroup TPrimeX] [AddCommGroup MapsXLoopF]
variable [AddCommGroup PiDLoopF] [AddCommGroup HnextNext]

/-- First line of (4.27): concatenate the degree-zero comparison, the
orientation-dependent sphere evaluation, and the homotopy--homology
identification for `F`. -/
def sphereTauComparison
    (thetaX : TauX ≃ₗ[ℤ] MapsXF)
    (orientedSphereEvaluation : MapsXF ≃ₗ[ℤ] PiDF)
    (fiberHomotopyHomology : PiDF ≃ₗ[ℤ] Hnext) :
    TauX ≃ₗ[ℤ] Hnext :=
  (thetaX.trans orientedSphereEvaluation).trans fiberHomotopyHomology

/-- Second line of (4.27). -/
def sphereTPrimeComparison
    (loopComparison : TPrimeX ≃ₗ[ℤ] MapsXLoopF)
    (orientedSphereEvaluation : MapsXLoopF ≃ₗ[ℤ] PiDLoopF)
    (loopFiberHomotopyHomology : PiDLoopF ≃ₗ[ℤ] HnextNext) :
    TPrimeX ≃ₗ[ℤ] HnextNext :=
  (loopComparison.trans orientedSphereEvaluation).trans
    loopFiberHomotopyHomology

end SphereCorollary

end GeneralSphereT.Section4
