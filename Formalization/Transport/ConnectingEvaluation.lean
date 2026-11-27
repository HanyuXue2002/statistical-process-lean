import Formalization.Transport.AlternatingEvaluation
import Formalization.Section4ReducedFreeHomologyShift
import Mathlib.Algebra.Homology.ConcreteCategory

/-! Evaluation of the connecting isomorphism on an actual lifted chain.
All homology objects below use integral modules. -/
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1400000
noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex OpenDisk AlgebraicTopology
open GeneralSphereT.StandardModels
namespace GeneralSphereT.Transport.RelativeChains

private instance : integralModules.EssSurj where
  mem_essImage M := by
    let F := forget₂ (ModuleCat ℤ) AddCommGrpCat
    refine ⟨F.obj M,⟨F.preimageIso ?_⟩⟩
    exact Iso.refl _
private instance : integralModules.IsEquivalence where

abbrev altSequence (G : AddCommGrpCat.{0}) (q : ℕ) :=
  (FAlternatingKernelSequence G q).map (integralModules.mapHomologicalComplex (.down ℕ))

theorem altSequence_exact (G : AddCommGrpCat.{0}) (q : ℕ) : (altSequence G q).ShortExact := by
  rw [HomologicalComplex.shortExact_iff_degreewise_shortExact]
  intro n
  exact (((HomologicalComplex.shortExact_iff_degreewise_shortExact _).mp (FAlternatingKernelSequence_shortExact G q)) n).map_of_exact integralModules

private theorem middle_zero (G : AddCommGrpCat.{0}) (q n : ℕ) : IsZero ((altSequence G q).X₂.homology n) := by
  let H := integralModules.mapHomotopy (DoldKanDiskContraction.reducedFreeLAlternatingContractingHomotopy G q)
  have e := H.homologyMap_eq n
  rw [Functor.map_zero,(integralModules.mapHomologicalComplex (.down ℕ)).map_id,HomologicalComplex.homologyMap_zero,HomologicalComplex.homologyMap_id] at e
  rw [IsZero.iff_id_eq_zero]
  exact e.symm

def connectingEquiv (G : AddCommGrpCat.{0}) (q n : ℕ) :
    (altSequence G q).X₃.homology (n+1) ≃ₗ[ℤ] (altSequence G q).X₁.homology n := by
  let hS := altSequence_exact G q
  let δ := hS.δ (n+1) n (by simp)
  have : Mono δ := by
    rw [(hS.homology_exact₃ (n+1) n (by simp)).mono_g_iff]
    exact (middle_zero G q (n+1)).eq_of_src _ _
  have : Epi δ := by
    rw [(hS.homology_exact₁ (n+1) n (by simp)).epi_f_iff]
    exact (middle_zero G q n).eq_of_tgt _ _
  letI := isIso_of_mono_of_epi δ
  exact (asIso δ).toLinearEquiv

def homologyClass {R : Type} [CommRing R] (C : ChainComplex (ModuleCat R) ℕ) (n : ℕ) (z : ChainSphere.cycles C n) :=
  ChainSphere.homologyQuotientEquiv C n ((LinearMap.range (ChainSphere.boundary C n)).mkQ z)

private theorem next_nat (n : ℕ) : (ComplexShape.down ℕ).next n=n-1 := by
  cases n <;> simp [ChainComplex.next_nat_zero,ChainComplex.next_nat_succ]

theorem homologyClass_as_cycles {R : Type} [CommRing R] (C : ChainComplex (ModuleCat R) ℕ) (n : ℕ) (z : ChainSphere.cycles C n) :
    homologyClass C n z = (C.homologyπ n) (C.cyclesMk z.val (n-1) (next_nat n) z.property) := by
  let S := C.sc' (n+1) n (n-1)
  let data := S.moduleCatLeftHomologyData
  let e := C.cyclesIsoSc' (n+1) n (n-1) (by simp) (next_nat n)
  let h := C.homologyIsoSc' (n+1) n (n-1) (by simp) (next_nat n)
  have a : data.π ≫ data.homologyIso.inv = data.cyclesIso.inv ≫ S.homologyπ := data.π_comp_homologyIso_inv
  have b : S.homologyπ ≫ h.inv=e.inv ≫ C.homologyπ n := C.π_homologyIsoSc'_inv _ _ _ _ _
  have c : e.inv (data.cyclesIso.inv z) = C.cyclesMk z.val (n-1) (next_nat n) z.property := by
    apply (Preadditive.mono_iff_injective (C.iCycles n)).mp inferInstance
    have h₁ := ConcreteCategory.congr_hom (C.cyclesIsoSc'_inv_iCycles (n+1) n (n-1) (by simp) (next_nat n)) (data.cyclesIso.inv z)
    have h₂ := ConcreteCategory.congr_hom data.cyclesIso_inv_comp_iCycles z
    exact (h₁.trans h₂).trans (C.i_cyclesMk z.val _ (next_nat n) z.property).symm
  exact (congrArg h.inv (ConcreteCategory.congr_hom a z)).trans
    ((ConcreteCategory.congr_hom b (data.cyclesIso.inv z)).trans (congrArg (C.homologyπ n) c))

/-- The connecting map takes the projected cycle of a lifted chain to its
literal boundary in the fibre. -/
theorem connecting_on_lift (G : AddCommGrpCat.{0}) (q n : ℕ)
    (z : ChainSphere.cycles (altSequence G q).X₃ (n+1))
    (w : (altSequence G q).X₂.X (n+1)) (y : ChainSphere.cycles (altSequence G q).X₁ n)
    (hg : (altSequence G q).g.f (n+1) w=z.val)
    (hf : (altSequence G q).f.f n y.val=(altSequence G q).X₂.d (n+1) n w) :
    connectingEquiv G q n (homologyClass _ (n+1) z)=homologyClass _ n y := by
  rw [homologyClass_as_cycles,homologyClass_as_cycles]
  exact (altSequence_exact G q).δ_apply (n+1) n (by simp) z.val z.property w hg y.val hf (n-1) (next_nat n)

end GeneralSphereT.Transport.RelativeChains

