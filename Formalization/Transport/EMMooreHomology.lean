import Formalization.Transport.ProjectedDifferential

/-! The quotient by literal EM boundaries and repetitions is the homology
of the normalized reduced-free Moore complex, with its actual simplex pairing. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open CategoryTheory Opposite Simplicial
namespace GeneralSphereT.Transport.Prism
open GeneralSphereT.StandardModels RelativeChains OpenDisk
variable {G : Type} [AddCommGroup G] (q d : ℕ)
private abbrev A := K (AddCommGrpCat.of G) q
abbrev normEM := target (reducedFree (A (G:=G) q))

theorem degenerate_of_nonDeg_zero {n : ℕ} (x : OpenDisk.PhaseDuality.Distribution (EM G q (n+1)))
    (hx : ∀ a, Nondeg q a → x a=0) : x ∈ degenerateSpan (A (G:=G) q) n := by
  classical
  rw [← Finsupp.sum_single x]
  apply Submodule.sum_mem
  intro a ha
  have ne : ¬Nondeg q a := fun hn => (Finsupp.mem_support_iff.mp ha) (hx a hn)
  simp only [Nondeg,not_forall,not_not] at ne
  obtain ⟨i,b,rfl⟩ := ne
  rw [show Finsupp.single ((A (G:=G) q).σ i b) (x ((A (G:=G) q).σ i b))=x ((A (G:=G) q).σ i b) • Finsupp.single ((A (G:=G) q).σ i b) 1 by simp]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i,b,rfl⟩)

def projectedCycle (x : emCycles (G:=G) q d) : ChainSphere.cycles (normEM (G:=G) q) (d+2) :=
  ⟨simplexProjection (A (G:=G) q) (d+2) x.val,by
    have h : emBoundary x.val ∈ degenerateSpan (A (G:=G) q) d := degenerate_of_nonDeg_zero q _ (fun a ha => by
      have e := DFunLike.congr_fun (show normalBoundary q d x.val=0 from x.property) ⟨a,ha⟩
      exact (normalBoundary_at q d x.val ⟨a,ha⟩).symm.trans e)
    exact (project_boundary (A (G:=G) q) (d+1) x.val).trans (project_kills_degeneracies (A (G:=G) q) d h)⟩

def includedCycle : ChainSphere.cycles (normEM (G:=G) q) (d+2) →ₗ[ℤ] emCycles (G:=G) q d where
  toFun z := ⟨(mooreInclusion (A (G:=G) q) (d+2) z.val).val,by
    apply normalBoundary_zero_of_coefficients
    intro a _
    have h := included_boundary (A (G:=G) q) (d+1) z.val
    have hz : (normEM (G:=G) q).d (d+2) (d+1) z.val=0 := z.property
    rw [hz,map_zero,Submodule.coe_zero] at h
    exact DFunLike.congr_fun h a⟩
  map_add' x y := Subtype.ext (congrArg (fun a : GeneralSphereT.PathAlgebra.RedDist (EM G q (d+2)) => a.val)
    ((mooreInclusion (A (G:=G) q) (d+2)).map_add x.val y.val))
  map_smul' r x := Subtype.ext (congrArg (fun a : GeneralSphereT.PathAlgebra.RedDist (EM G q (d+2)) => a.val)
    ((mooreInclusion (A (G:=G) q) (d+2)).map_smul r x.val))

private def classFromMoore := (emClass (G:=G) q d).comp (includedCycle q d)

theorem classFromMoore_surjective : Function.Surjective (classFromMoore (G:=G) q d) := by
  intro z
  obtain ⟨x,rfl⟩ := emClass_surj q d z
  refine ⟨projectedCycle q d x,Subtype.ext ?_⟩
  let D := degenerateSpan (A (G:=G) q) (d+1)
  have hD : D ≤ emRelations q d := le_sup_right
  apply (Submodule.Quotient.eq _).mpr
  apply hD
  exact (Submodule.Quotient.eq D).mp (class_of_projection (A (G:=G) q) (d+1) x.val)

theorem classFromMoore_kernel : LinearMap.ker (classFromMoore (G:=G) q d)=LinearMap.range (ChainSphere.boundary (normEM (G:=G) q) (d+2)) := by
  ext z
  constructor
  · intro hz
    have e := congrArg Subtype.val (show classFromMoore q d z=0 from hz)
    have he : (mooreInclusion (A (G:=G) q) (d+2) z.val).val ∈ emRelations q d := (Submodule.Quotient.mk_eq_zero _).mp e
    obtain ⟨_,⟨w,rfl⟩,u,hu,huv⟩ := Submodule.mem_sup.mp he
    refine ⟨simplexProjection (A (G:=G) q) (d+3) w,Subtype.ext ?_⟩
    have e₁ := congrArg (simplexProjection (A (G:=G) q) (d+2)) huv
    rw [map_add,show simplexProjection (A (G:=G) q) (d+2) u=0 from project_kills_degeneracies (A (G:=G) q) (d+1) hu,add_zero,project_include] at e₁
    exact (project_boundary (A (G:=G) q) (d+2) w).trans e₁
  · rintro ⟨w,rfl⟩
    apply Subtype.ext
    apply (Submodule.Quotient.mk_eq_zero _).mpr
    apply le_sup_left (b:=degenerateSpan (A (G:=G) q) (d+1))
    exact ⟨(mooreInclusion (A (G:=G) q) (d+3) w).val,included_boundary (A (G:=G) q) (d+2) w⟩

def mooreClassEquiv : ChainSphere.homologyQuotient (normEM (G:=G) q) (d+2) ≃ₗ[ℤ] CycleClasses (G:=G) q d :=
  (Submodule.quotEquivOfEq _ _ (classFromMoore_kernel q d).symm).trans
    ((classFromMoore q d).quotKerEquivOfSurjective (classFromMoore_surjective q d))

theorem mooreClassEquiv_mk (z : ChainSphere.cycles (normEM (G:=G) q) (d+2)) :
    mooreClassEquiv q d (Submodule.Quotient.mk z)=emClass q d (includedCycle q d z) := rfl

end GeneralSphereT.Transport.Prism

