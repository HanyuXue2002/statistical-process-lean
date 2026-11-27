import Formalization.OpenDisk.PhaseDualitySimplicial
import Formalization.Section4NativeTheta

set_option linter.style.header false

/-!
# Actual phase tables and genuine pointed simplicial mapping classes

This connects the integral duality of Proposition 2.1 to the existing,
proved simplicial mapping-class comparison.  The target is Mathlib's native
relative homotopy quotient.  It is not relabeled as sphere homology: that
further geometric comparison is a separate theorem.
-/

noncomputable section

open GeneralSphereT.PathAlgebra GeneralSphereT.SimplicialCochain
open GeneralSphereT.Section4 GeneralSphereT.StandardModels

namespace OpenDisk.PhaseDuality

universe u

variable {V G : Type u} [LinearOrder V] [Fintype V] [AddCommGroup G]
variable (K : AbstractSimplicialComplex V) (b : V) (n : ℕ)

local instance : Fintype (NonemptySimplex K) := Fintype.ofFinite _

local instance : LinearOrder (Simplex K n) := by
  classical
  exact linearOrderOfSTO WellOrderingRel

/-- The literal full-distribution obstruction group agrees with the
genuine based simplicial mapping classes under reduced cohomology vanishing. -/
def fullTauNativeEquivOfReduced
    (hred : ReducedCohomologyZeroAt (G := G) K b n) :
    simplicialFullTau (G := G) K n ≃ₗ[ℤ]
      NativePointedHomotopyClasses K b (AddCommGrpCat.of G) (n + 1) := by
  letI : Nonempty (NonemptySimplex K) := ⟨coneApexSimplex K b⟩
  exact (fullTauEquivExistingTau
    (fun σ : NonemptySimplex K => facesIn K n σ)
    (coboundaryToRange (G := G) K n) (facetRestrictionData (G := G) K n)
    (coboundaryToRange_surjective K n)).trans
      (nativeThetaOfReduced K b n hred)

/-- A proved mapping-class version of Theorem 2.4, dualized all the way
back to the original closed local phase-table quotient. -/
def closedPhaseQuotientNativeEquivOfReduced
    (hred : ReducedCohomologyZeroAt (G := G) K b n) :
    (simplicialClosedSPT (G := G) K n ⧸ simplicialFacetCurvaturePhases (G := G) K n) ≃ₗ[ℤ]
      (NativePointedHomotopyClasses K b (AddCommGrpCat.of G) (n + 1) →ₗ[ℤ] Phase) :=
  (simplicialClosedSPTQuotientEquiv K n).trans
    (LinearEquiv.arrowCongr (fullTauNativeEquivOfReduced K b n hred)
      (LinearEquiv.refl ℤ Phase))

/-- Character precomposition by an integral isomorphism is a homeomorphism
for pointwise convergence; this needs no finite generation hypothesis. -/
def characterHomeomorphOfLinearEquiv {A B : Type*}
    [AddCommGroup A] [AddCommGroup B] (e : A ≃ₗ[ℤ] B) :
    (A →ₗ[ℤ] Phase) ≃ₜ (B →ₗ[ℤ] Phase) where
  toEquiv := (LinearEquiv.arrowCongr e (LinearEquiv.refl ℤ Phase)).toEquiv
  continuous_toFun := by
    apply continuous_induced_rng.mpr
    apply continuous_pi
    intro b
    exact continuous_character_evaluation (e.symm b)
  continuous_invFun := by
    apply continuous_induced_rng.mpr
    apply continuous_pi
    intro a
    exact continuous_character_evaluation (e a)

/-- The same mapping-class duality retains the literal quotient topology
on phase tables and pointwise topology on the character group. -/
def closedPhaseQuotientNativeHomeomorphOfReduced
    (hred : ReducedCohomologyZeroAt (G := G) K b n) :
    (simplicialClosedSPT (G := G) K n ⧸ simplicialFacetCurvaturePhases (G := G) K n) ≃ₜ
      (NativePointedHomotopyClasses K b (AddCommGrpCat.of G) (n + 1) →ₗ[ℤ] Phase) :=
  (simplicialClosedSPTQuotientHomeomorph K n).trans
    (characterHomeomorphOfLinearEquiv (fullTauNativeEquivOfReduced K b n hred))

end OpenDisk.PhaseDuality
