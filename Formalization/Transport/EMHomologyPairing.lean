import Formalization.Transport.EMMooreHomology
import Formalization.Transport.ConnectingEvaluation

/-! The ordinary homology pairing, evaluated on the actual alternating chain. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open CategoryTheory HomologicalComplex Opposite Simplicial OpenDisk
namespace GeneralSphereT.Transport.Prism
open GeneralSphereT.StandardModels GeneralSphereT.PathAlgebra RelativeChains PhaseDuality

private theorem map_homologyClass {R : Type} [CommRing R] {C D : ChainComplex (ModuleCat R) ℕ}
    (f : C ⟶ D) (n : ℕ) (z : ChainSphere.cycles C n) :
    homologyMap f n (homologyClass C n z)=homologyClass D n (imageCycle n f z) := by
  have hn : (ComplexShape.down ℕ).next n=n-1 := by
    cases n <;> simp [ChainComplex.next_nat_zero,ChainComplex.next_nat_succ]
  rw [homologyClass_as_cycles,homologyClass_as_cycles]
  let c := C.cyclesMk z.val (n-1) hn z.property
  let y := imageCycle n f z
  have eq : cyclesMap f n c = D.cyclesMk y.val (n-1) hn y.property := by
    apply (Preadditive.mono_iff_injective (D.iCycles n)).mp inferInstance
    exact (ConcreteCategory.congr_hom (cyclesMap_i f n) c).trans
      ((congrArg (f.f n) (C.i_cyclesMk z.val _ hn z.property)).trans (D.i_cyclesMk y.val _ hn y.property).symm)
  exact (ConcreteCategory.congr_hom (homologyπ_naturality f n) c).trans (congrArg (D.homologyπ n) eq)

variable {G : Type} [AddCommGroup G] (q d : ℕ)
private abbrev A := K (AddCommGrpCat.of G) q

def altEMEquiv : (altChains.obj (reducedFree (A (G:=G) q))).homology (d+2) ≃ₗ[ℤ] CycleClasses (G:=G) q d :=
  ((normalization (reducedFree (A (G:=G) q))).toHomologyIso (d+2)).symm.toLinearEquiv.trans
    ((ChainSphere.homologyQuotientEquiv _ _).symm.trans (mooreClassEquiv q d))

theorem altEM_pairing (ω : NormalizedCocycle G q d)
    (w : ChainSphere.cycles (altChains.obj (reducedFree (A (G:=G) q))) (d+2)) :
    cocycleCharacter q d ω (altEMEquiv q d (homologyClass _ (d+2) w))=evaluate ω.val w.val.val := by
  let f := (normalization (reducedFree (A (G:=G) q))).inv
  change cocycleCharacter q d ω (mooreClassEquiv q d ((ChainSphere.homologyQuotientEquiv _ _).symm
    (homologyMap f (d+2) (homologyClass _ (d+2) w))))=_
  rw [map_homologyClass]
  simp only [homologyClass,LinearEquiv.symm_apply_apply]
  change evaluate ω.val (mooreInclusion (A (G:=G) q) (d+2) (mooreProjection _ _ w.val)).val=_
  let D := degenerateSpan (A (G:=G) q) (d+1)
  have h : D ≤ LinearMap.ker (evaluate ω.val) :=
    le_trans (show D ≤ emRelations q d from le_sup_right) ((annihilates_emRelations q d ω.val).mpr ω.property)
  have eq := congrArg (D.liftQ (evaluate ω.val) h) (class_of_projection (A (G:=G) q) (d+1) w.val.val)
  change evaluate ω.val (mooreInclusion (A (G:=G) q) (d+2) (mooreProjection _ _ (reduceDist w.val.val))).val=_ at eq
  rw [reduceDist_red] at eq
  exact eq

theorem evaluate_reduction (ω : NormalizedCocycle G q d) (z : Distribution (EM G q (d+2))) :
    evaluate ω.val (reduceDist z).val=evaluate ω.val z := by
  have hz := ω.property.2 (0 : Fin (d+2)) (0 : EM G q (d+1))
  rw [map_zero] at hz
  rw [reduceDist_val,map_sub,evaluate_single,hz,smul_zero,sub_zero]

end GeneralSphereT.Transport.Prism
