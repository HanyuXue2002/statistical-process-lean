import Formalization.Transport.EMIntegralCycles

/-! The explicit integral map whose dual is the prism classification map. -/
noncomputable section
namespace GeneralSphereT.Transport.Prism
open GeneralSphereT.SimplicialCochain OpenDisk.PhaseDuality
variable {G V : Type} [AddCommGroup G] [LinearOrder V] [Fintype V]
variable (X : AbstractSimplicialComplex V) (q d : ℕ)
local instance integralFacetFintype : Fintype (Simplex X d) := Fintype.ofFinite _

private def cycleMap (coeff : Simplex X d → ℤ) (hz : boundary (orientedFacets X d coeff)=0) :
    LinearMap.ker (readBoundary (topFacetData (G:=G) X d q)) →ₗ[ℤ] emCycles (G:=G) (q+1) d :=
  ((measuredChain X q d coeff).comp (LinearMap.ker _).subtype).codRestrict _
    (fun y => normalBoundary_zero_of_coefficients _ _ _ (measuredChain_is_cycle X q d coeff hz y))

theorem measured_relation (b : V) (hred : ReducedCohomologyZeroAt (G:=G) X b q)
    (coeff : Simplex X d → ℤ) (hz : boundary (orientedFacets X d coeff)=0)
    (r : Distribution (Triangle (Cochain X q G) (State (G:=G) X q))) (hr : r ∈ relations (topFacetData X d q)) :
    measuredChain X q d coeff r ∈ emRelations (q+1) d := by
  apply (mem_iff_annihilator _ _).mpr
  intro χ hχ
  let ω := phaseTableEquiv.symm χ
  have he : evaluate ω=χ := phaseTableEquiv.apply_symm_apply _
  have hc := (annihilates_emRelations (q+1) d ω).mp (he ▸ hχ)
  let m := physicalPrismMultiplier X q d b hred ω hc.1 hc.2 coeff hz
  have annih := (character_iff _ m.value).mpr ⟨m,rfl⟩
  rw [← he]
  exact (LinearMap.congr_fun (evaluated_measurement X q d coeff ω) r).trans (annih r hr)

/-- The integer chain from a literal transport process, modulo boundaries and
degenerate simplices. Both the process relations and its cycle condition are proved. -/
def integralPrism (b : V) (hred : ReducedCohomologyZeroAt (G:=G) X b q)
    (coeff : Simplex X d → ℤ) (hz : boundary (orientedFacets X d coeff)=0) :
    IntegralProcesses (topFacetData (G:=G) X d q) →ₗ[ℤ] CycleClasses (G:=G) (q+1) d :=
  (identitiesInInvariant _ _).liftQ ((emClass (q+1) d).comp (cycleMap X q d coeff hz)) (by
    intro r hr
    apply Subtype.ext
    change (emRelations (q+1) d).mkQ (measuredChain X q d coeff r.val)=0
    exact (Submodule.Quotient.mk_eq_zero _).mpr (measured_relation X q d b hred coeff hz r.val hr))

/-- The square commutes for the specified orientation, multiplication order and minus sign. -/
theorem prism_pairing (b : V) (hred : ReducedCohomologyZeroAt (G:=G) X b q)
    (coeff : Simplex X d → ℤ) (hz : boundary (orientedFacets X d coeff)=0)
    (a : NormalizedEMCohomology G (q+1) d) :
    multiplierClassification (topFacetData X d q) (prismClass X q d b hred coeff hz a) =
      (normalizedCharacterEquiv (q+1) d a).comp (integralPrism X q d b hred coeff hz) := by
  induction a using Quotient.inductionOn with | _ ω =>
    apply LinearMap.ext
    intro x
    obtain ⟨y,rfl⟩ := (identitiesInInvariant _ _).mkQ_surjective x
    change evaluate (fun t => physicalPrism X q d ω.val coeff t.1 t.2.1 t.2.2) y.val =
      evaluate ω.val (measuredChain X q d coeff y.val)
    exact (LinearMap.congr_fun (evaluated_measurement X q d coeff ω.val) y.val).symm

/-- A single local phase table strictifies the actual formula precisely when
the cocycle has zero period on every measured integral cycle. -/
theorem prism_strict_iff_zero_periods (ω : EM G (q+1) (d+2) → Phase) (coeff : Simplex X d → ℤ) :
    Equivalent (topFacetData (G:=G) X d q) (fun t => physicalPrism X q d ω coeff t.1 t.2.1 t.2.2) (fun _ => 0) ↔
      ∀ y : LinearMap.ker (readBoundary (topFacetData (G:=G) X d q)), evaluate ω (measuredChain X q d coeff y.val)=0 := by
  rw [equivalent_iff]
  have zeroEval : evaluate (fun _ : Triangle (Cochain X q G) (State (G:=G) X q) => 0)=0 :=
    (phaseTableEquiv (X:=Triangle (Cochain X q G) (State (G:=G) X q))).map_zero
  rw [zeroEval]
  constructor
  · intro h y
    exact (LinearMap.congr_fun (evaluated_measurement X q d coeff ω) y.val).trans (h y.val y.property).symm
  · intro h x hx
    exact ((LinearMap.congr_fun (evaluated_measurement X q d coeff ω) x).symm.trans (h ⟨x,hx⟩)).symm

/-- Exact integral criterion for the outstanding classification assertion. -/
theorem prism_bijective_iff_integral (b : V) (hred : ReducedCohomologyZeroAt (G:=G) X b q)
    (coeff : Simplex X d → ℤ) (hz : boundary (orientedFacets X d coeff)=0) :
    Function.Bijective (prismClass X q d b hred coeff hz) ↔ Function.Bijective (integralPrism X q d b hred coeff hz) := by
  let M := multiplierClassification (topFacetData (G:=G) X d q)
  let H := normalizedCharacterEquiv (G:=G) (q+1) d
  let p := prismClass X q d b hred coeff hz
  let f := integralPrism X q d b hred coeff hz
  let dual := fun χ : CycleClasses (G:=G) (q+1) d →ₗ[ℤ] Phase => χ.comp f
  have eq : M ∘ p = dual ∘ H := funext (prism_pairing X q d b hred coeff hz)
  change Function.Bijective p ↔ Function.Bijective f
  rw [← Equiv.comp_bijective p M,eq,Equiv.bijective_comp]
  exact dual_bijective_iff f

end GeneralSphereT.Transport.Prism
