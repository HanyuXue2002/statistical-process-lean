import Formalization.OpenDisk.PhaseDualityChainSphereInvariance
import Mathlib.Algebra.Homology.DerivedCategory.KProjective
import Mathlib.Algebra.Category.ModuleCat.Projective

/-! Evaluation of chain homotopy classes on an integral fundamental cycle.
For a degreewise projective source it suffices to check its integral homology. -/
noncomputable section
open CategoryTheory HomologicalComplex OpenDisk
namespace GeneralSphereT.Transport
variable {R : Type} [CommRing R] (C A : ChainComplex (ModuleCat R) ℕ) (n : ℕ)

private theorem sphere_projective (i : ℕ) : Projective ((ChainSphere.sphere (R:=R) n).X i) := by
  by_cases h : i=n
  · subst i
    apply Projective.of_iso (singleObjXSelf (.down ℕ) n (ModuleCat.of R R)).symm
    exact (IsProjective.iff_projective (R:=R) R).mp inferInstance
  · exact (isZero_single_obj_X (.down ℕ) n (ModuleCat.of R R) i h).projective

def fundamentalSphereEquiv [∀ i, Projective (C.X i)] (z : ChainSphere.cycles C n)
    (h : QuasiIso (ChainSphere.mapOfCycle C n z)) : HomotopyEquiv (ChainSphere.sphere (R:=R) n) C := by
  letI := sphere_projective (R:=R) n
  exact ((ChainComplex.quasiIso_iff_of_projective _).mp h).choose

private theorem fundamentalSphereEquiv_hom [∀ i, Projective (C.X i)] (z : ChainSphere.cycles C n)
    (h : QuasiIso (ChainSphere.mapOfCycle C n z)) : (fundamentalSphereEquiv C n z h).hom=ChainSphere.mapOfCycle C n z := by
  letI := sphere_projective (R:=R) n
  exact ((ChainComplex.quasiIso_iff_of_projective _).mp h).choose_spec

/-- The fundamental cycle need only induce the homology of ℤ[n]. -/
def fundamentalEvaluation [∀ i, Projective (C.X i)] (z : ChainSphere.cycles C n)
    (h : QuasiIso (ChainSphere.mapOfCycle C n z)) :
    ChainClasses.classes C A ≃ₗ[R] A.homology n :=
  ChainClasses.equivHomologyOfSphere (C:=C) (A:=A) n (fundamentalSphereEquiv C n z h).symm

theorem fundamentalEvaluation_mk [∀ i, Projective (C.X i)] (z : ChainSphere.cycles C n)
    (h : QuasiIso (ChainSphere.mapOfCycle C n z)) (u : C ⟶ A) :
    fundamentalEvaluation C A n z h (Submodule.Quotient.mk u) =
      ChainSphere.mapClassesEquivHomology A n (Submodule.Quotient.mk (ChainSphere.mapOfCycle C n z ≫ u)) := by
  change ChainSphere.mapClassesEquivHomology A n (Submodule.Quotient.mk ((fundamentalSphereEquiv C n z h).hom ≫ u)) = _
  rw [fundamentalSphereEquiv_hom]

end GeneralSphereT.Transport
