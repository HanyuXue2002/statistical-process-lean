import Formalization.Transport.PrismGauge

/-! A transport process measures an explicit integral EM chain. Its ordinary
boundary has zero multiplicity on every nondegenerate simplex. -/
noncomputable section
open CategoryTheory Opposite Simplicial
namespace GeneralSphereT.Transport.Prism
open GeneralSphereT.SimplicialCochain GeneralSphereT.StandardModels OpenDisk.PhaseDuality
variable {G : Type} [AddCommGroup G] {Y : Type*}

def simplexChain {q : ℕ} (field : (Fin (q+1) → Y) → G) (p : ℕ) :
    Chains Y →ₗ[ℤ] Distribution (EM G (q+1) p) :=
  Finsupp.linearCombination ℤ fun xs => if h : xs.length=p+1 then
    Finsupp.single (classifyingValue field (fun i => xs.get (i.cast h.symm))) 1 else 0

theorem evaluate_simplexChain {q p : ℕ} (field : (Fin (q+1) → Y) → G) (ω : EM G (q+1) p → Phase) :
    (evaluate ω).comp (simplexChain field p)=pullCochain field ω := by
  apply Finsupp.lhom_ext'
  intro xs
  apply LinearMap.ext_ring
  change evaluate ω (simplexChain field p (gen xs))=pullCochain field ω (gen xs)
  simp only [gen,simplexChain,Finsupp.linearCombination_single,one_smul,pullCochain,evaluate_single,one_zsmul,homogeneous]
  split <;> simp

def emBoundary {q p : ℕ} : Distribution (EM G q (p+1)) →ₗ[ℤ] Distribution (EM G q p) :=
  Finsupp.linearCombination ℤ fun x => ∑ i : Fin (p+2), ((-1:ℤ)^i.val) • Finsupp.single ((K (AddCommGrpCat.of G) q).δ i x) 1

theorem evaluate_emBoundary {q p : ℕ} (θ : EM G q p → Phase) :
    (evaluate θ).comp emBoundary=evaluate (phaseDifferential θ) := by
  ext x
  simp [emBoundary,phaseDifferential]

variable {V : Type} [LinearOrder V] [Fintype V] (X : AbstractSimplicialComplex V) (q d : ℕ)
local instance measuredFacetFintype : Fintype (Simplex X d) := Fintype.ofFinite _

/-- Signed sum of the oriented time triangles, projected simplex by simplex to K. -/
def measuredChain (coeff : Simplex X d → ℤ) :
    Distribution (Triangle (Cochain X q G) (State (G:=G) X q)) →ₗ[ℤ] Distribution (EM G (q+1) (d+2)) :=
  Finsupp.linearCombination ℤ fun x =>
    let v := liftState X q x.2.2
    (-(simplexChain (affineField X q) (d+2) (triangle (layerOf X q v) (layerOf X q (v+x.2.1))
      (layerOf X q (v+x.2.1+x.1)) (orientedFacets X d coeff))))

theorem evaluated_measurement (coeff : Simplex X d → ℤ) (ω : EM G (q+1) (d+2) → Phase) :
    (evaluate ω).comp (measuredChain X q d coeff)=evaluate (fun x => physicalPrism X q d ω coeff x.1 x.2.1 x.2.2) := by
  apply Finsupp.lhom_ext'
  intro x
  apply LinearMap.ext_ring
  change evaluate ω (measuredChain X q d coeff (Finsupp.single x 1))=evaluate _ (Finsupp.single x 1)
  simp only [measuredChain,Finsupp.linearCombination_single,one_smul,map_neg,evaluate_single,one_zsmul]
  apply congrArg Neg.neg
  exact LinearMap.congr_fun (evaluate_simplexChain (affineField X q) ω) _

theorem measurement_annihilates_coboundaries (coeff : Simplex X d → ℤ) (hz : boundary (orientedFacets X d coeff)=0)
    (y : LinearMap.ker (readBoundary (topFacetData (G:=G) X d q))) (θ : EM G (q+1) (d+1) → Phase)
    (hn : NormalizedOnEM θ) : evaluate θ (emBoundary (measuredChain X q d coeff y.val))=0 := by
  have e := LinearMap.congr_fun (evaluate_emBoundary θ) (measuredChain X q d coeff y.val)
  have e' := LinearMap.congr_fun (evaluated_measurement X q d coeff (phaseDifferential θ)) y.val
  simp only [LinearMap.comp_apply] at e e'
  rw [e,e']
  obtain ⟨f,hf⟩ := physicalEdge_localTable X q d θ hn coeff
  have eq : Equivalent (topFacetData (G:=G) X d q) (fun _ => 0)
      (fun x => physicalPrism X q d (phaseDifferential θ) coeff x.1 x.2.1 x.2.2) := by
    refine ⟨f,fun t s a => ?_⟩
    simp [physicalPrism_of_coboundary X q d θ coeff hz,hf]
  have h := (equivalent_iff _ _ _).mp eq y.val y.property
  exact h.trans (LinearMap.congr_fun (phaseTableEquiv (X:=Triangle (Cochain X q G) (State (G:=G) X q))).map_zero y.val)

private theorem single_phase {E : Type*} [DecidableEq E] (z : Distribution E) (a : E) (t : Phase) :
    evaluate (fun x => if x=a then t else 0) z = z a • t := by
  classical
  induction z using Finsupp.induction_linear with
  | zero => simp
  | add _ _ ha hb => simp [ha,hb,add_smul]
  | single x n => by_cases h : x=a <;> simp [h,Finsupp.single_apply]

/-- In integer coefficients, the measured chain is a cycle in the normalized
simplicial chains of K. This tests every nondegenerate boundary coefficient. -/
theorem measuredChain_is_cycle (coeff : Simplex X d → ℤ) (hz : boundary (orientedFacets X d coeff)=0)
    (y : LinearMap.ker (readBoundary (topFacetData (G:=G) X d q))) (a : EM G (q+1) (d+1))
    (ha : ∀ (i : Fin (d+1)) (b : EM G (q+1) d), (K (AddCommGrpCat.of G) (q+1)).σ i b ≠ a) :
    (emBoundary (measuredChain X q d coeff y.val)) a=0 := by
  classical
  let k := (emBoundary (measuredChain X q d coeff y.val)) a
  let N := k.natAbs+1
  have hN : 0<N := Nat.succ_pos _
  let t : Phase := ((1/(N:ℝ) : ℝ) : Phase)
  have ht : addOrderOf t=N := AddCircle.addOrderOf_period_div (p:=(1:ℝ)) hN
  let θ := fun x => if x=a then t else 0
  have hn : NormalizedOnEM θ := fun i b => if_neg (ha i b)
  have h := measurement_annihilates_coboundaries X q d coeff hz y θ hn
  change evaluate (fun x => if x=a then t else 0) _=0 at h
  rw [single_phase] at h
  change k • t=0 at h
  have dv := addOrderOf_dvd_iff_zsmul_eq_zero.mpr h
  rw [ht] at dv
  have D : N ∣ k.natAbs := Int.natCast_dvd_natCast.mp (Int.dvd_natAbs.mpr dv)
  by_contra ne
  have hpos : 0<k.natAbs := Int.natAbs_pos.mpr ne
  have := Nat.le_of_dvd hpos D
  omega

end GeneralSphereT.Transport.Prism
