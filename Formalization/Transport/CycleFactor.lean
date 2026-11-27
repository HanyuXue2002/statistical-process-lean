import Formalization.Transport.PrimitiveComparison

noncomputable section
open scoped BigOperators
namespace GeneralSphereT.Transport
open GeneralSphereT.PathAlgebra GeneralSphereT.PathAlgebra.FacetRestrictionData OpenDisk.PhaseDuality
variable {C B F : Type*} [AddCommGroup C] [AddCommGroup B] [Fintype F]
variable {S A : F → Type*} [∀ i, AddCommGroup (S i)] [∀ i, AddCommGroup (A i)]
variable {d : C →+ B} (L : FacetRestrictionData (Facet:=F) (CAt:=S) (BAt:=A) d)

theorem cycle_factor (χ : RedDist C →ₗ[ℤ] Phase) (hz : ∀ z : Zprim L, χ z.val = 0) :
    ∃ (k : B → Phase) (u : ∀ i, S i → Phase),
      ∀ v, χ (redBracket v) = k (d v) + ∑ i, u i (L.primitiveRes i v) := by
  classical
  let joint := (mapRedDist d).prod (LinearMap.pi (restrictRedDist L))
  have hk : LinearMap.ker joint = Zprim L := by
    ext p
    simp [joint,Zprim,Rprim,locallyZeroRedDist,LinearMap.mem_ker,funext_iff]
  obtain ⟨ψ,hψ⟩ := (annihilates_kernel_iff joint χ).mp (fun p hp => hz ⟨p,hk ▸ hp⟩)
  let U := ψ.comp (LinearMap.inr ℤ _ _)
  refine ⟨fun a => ψ (redBracket a,0),fun i x => U (Pi.single i (redBracket x)),fun v => ?_⟩
  have e := LinearMap.congr_fun hψ (redBracket v)
  rw [← e]
  have localRead : LinearMap.pi (restrictRedDist L) (redBracket v) =
      fun i => redBracket (L.primitiveRes i v) := by
    funext i
    exact mapRedDist_redBracket _ v
  change ψ (mapRedDist d (redBracket v),LinearMap.pi (restrictRedDist L) (redBracket v)) = _
  rw [localRead,mapRedDist_redBracket]
  rw [← map_sum,Finset.univ_sum_single]
  simpa [U] using map_add ψ (redBracket (d v),0) (0,fun i => redBracket (L.primitiveRes i v))

theorem vacuum_local (m : Multiplier L) :
    ∃ o : ∀ i, S i → S i → Phase,
      ∀ s v, m.value (s,v,0) = ∑ i, o i (L.primitiveRes i s) (L.primitiveRes i v) := by
  classical
  obtain ⟨f,hf⟩ := m.localTable
  refine ⟨fun i s v => if s=0 ∨ v=0 then 0 else f ⟨i,s,v,0⟩,fun s v => ?_⟩
  rw [hf]
  simp only [triangleRead,map_sum]
  apply Finset.sum_congr rfl
  intro i _
  split <;> simp_all

/-- Ambiguity of the splitting of a fixed multiplier: a configuration
potential and an additive character on the full group of moves. -/
theorem cocycle_potential (hd : Function.Surjective d) (h : C → B → Phase)
    (hh : ∀ s t a, h s a + h t (a+d s) = h (s+t) a) :
    ∃ (k : B → Phase) (ψ : C →ₗ[ℤ] Phase), ∀ v, h v 0 = k (d v) + ψ v := by
  let ζ : d.ker →+ Phase := {
    toFun := fun z => h z 0
    map_zero' := by have e := hh 0 0 0; simpa using e
    map_add' := fun z w => by
      have e := hh z w 0
      simpa [AddMonoidHom.mem_ker.mp z.property] using e.symm }
  obtain ⟨ψ,hψ⟩ := extend_character (LinearMap.ker d.toIntLinearMap) ζ.toIntLinearMap
  choose v hv using hd
  refine ⟨fun a => h (v a) 0 - ψ (v a),ψ,fun x => ?_⟩
  let z : d.ker := ⟨x-v (d x), by simp [hv]⟩
  have e := hh z (v (d x)) 0
  have ez : d (z:C) = 0 := z.property
  have ex : (z:C) + v (d x) = x := sub_add_cancel _ _
  rw [ez,add_zero,ex] at e
  have es : ψ (z:C) = h z 0 := LinearMap.congr_fun hψ z
  rw [← es] at e
  change ψ (x-v (d x)) + _ = _ at e
  rw [map_sub] at e
  dsimp only
  rw [← e]
  abel

end GeneralSphereT.Transport

