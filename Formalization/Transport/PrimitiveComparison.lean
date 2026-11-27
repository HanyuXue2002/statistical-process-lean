import Formalization.Transport.VacuumSplitting

/-! Pairing with the strict primitive quotient from the existing sphere proofs. -/
noncomputable section
open scoped BigOperators
namespace GeneralSphereT.Transport
open GeneralSphereT.PathAlgebra GeneralSphereT.PathAlgebra.FacetRestrictionData OpenDisk.PhaseDuality

variable {C B : Type*} [AddCommGroup C] [AddCommGroup B]
variable {F : Type*} [Fintype F] {S A : F → Type*}
variable [∀ i, AddCommGroup (S i)] [∀ i, AddCommGroup (A i)]
variable {d : C →+ B}
variable (L : FacetRestrictionData (Facet := F) (CAt := S) (BAt := A) d)

def onEdges {I X : Type*} [AddCommGroup I] (h : I → X → Phase) (h0 : ∀ x, h 0 x = 0) :
    Path I X →ₗ[ℤ] Phase :=
  (zeroIncrement I X).liftQ (evaluate fun p : I × X => h p.1 p.2) (by
    rw [zeroIncrement,Submodule.span_le]
    rintro _ ⟨x,rfl⟩
    simp [h0])

@[simp] theorem onEdges_edge {I X : Type*} [AddCommGroup I] (h : I → X → Phase) (h0)
    (s : I) (x : X) : onEdges h h0 (edge s x) = h s x := by
  simp [onEdges,edge,rawEdge]

private theorem extEdges {I X : Type*} [AddCommGroup I] {f g : Path I X →ₗ[ℤ] Phase}
    (h : ∀ s x, f (edge s x) = g (edge s x)) : f = g := by
  have eq : f.comp (zeroIncrement I X).mkQ = g.comp (zeroIncrement I X).mkQ := by
    apply Finsupp.lhom_ext'
    rintro ⟨s,x⟩
    apply LinearMap.ext_ring
    exact h s x
  ext u
  exact LinearMap.congr_fun eq _

/-- Exact path-factorization criterion for the old denominator. -/
theorem annihilates_primitive_iff (χ : RedDist C →ₗ[ℤ] Phase) :
    χ ∈ annihilator (Bprim L) ↔
      ∃ (H : Path C B →ₗ[ℤ] Phase) (O : ∀ i, Path (S i) (S i) →ₗ[ℤ] Phase),
        ∀ s v, χ (redBracket (v+s)) - χ (redBracket v) =
          H (edge s (d v)) - ∑ i, O i (edge (L.primitiveRes i s) (L.primitiveRes i v)) := by
  classical
  let joint := (mapDPath d).prod (LinearMap.pi (restrictPrimitivePath L))
  have hk : LinearMap.ker joint = relationPaths L := by
    rw [relationPaths_eq,locallyZeroPrimitivePath]
    ext p
    simp [joint,LinearMap.mem_ker,funext_iff]
  constructor
  · intro h
    obtain ⟨ψ,hψ⟩ := (annihilates_kernel_iff joint (χ.comp (primitiveReducedBoundary C))).mp
      (fun p hp => h _ ⟨p,hk ▸ hp,rfl⟩)
    let H := ψ.comp (LinearMap.inl ℤ _ _)
    let U := ψ.comp (LinearMap.inr ℤ _ _)
    refine ⟨H,fun i => -(U.comp (LinearMap.single ℤ _ i)),fun s v => ?_⟩
    have e := LinearMap.congr_fun hψ (edge s v)
    let y := fun i => edge (L.primitiveRes i s) (L.primitiveRes i v)
    change ψ (mapDPath d (edge s v),fun i => restrictPrimitivePath L i (edge s v)) = _ at e
    simp only [LinearMap.comp_apply,restrictPrimitivePath,mapPath_edge,primitiveReducedBoundary,
      reducedBoundary_edge,AddMonoidHom.id_apply,map_sub] at e
    rw [← e]
    change ψ (edge s (d v),y) = ψ (edge s (d v),0) - ∑ i, -(U (Pi.single i (y i)))
    rw [Finset.sum_neg_distrib,sub_neg_eq_add,← map_sum,Finset.univ_sum_single]
    simpa [U] using map_add ψ (edge s (d v),0) (0,y)
  · rintro ⟨H,O,h⟩ u ⟨p,hp,rfl⟩
    have e : χ.comp (primitiveReducedBoundary C) =
        H.comp (mapDPath d) - ∑ i, (O i).comp (restrictPrimitivePath L i) := by
      apply extEdges
      intro s v
      simpa [restrictPrimitivePath,primitiveReducedBoundary,LinearMap.sum_apply] using h s v
    have hr i : restrictPrimitivePath L i p = 0 :=
      (Submodule.mem_iInf (fun j => LinearMap.ker (restrictPrimitivePath L j))).mp hp.2.2 i
    have e' := LinearMap.congr_fun e p
    simpa [LinearMap.sum_apply,hr,(show mapDPath d p = 0 from hp.2.1)] using e'

def potentialCharacter (β : C → Phase) : RedDist C →ₗ[ℤ] Phase :=
  (evaluate β).comp (RedDist C).subtype

@[simp] theorem potentialCharacter_bracket (β : C → Phase) (v : C) :
    potentialCharacter β (redBracket v) = β v - β 0 := by
  simp [potentialCharacter,redBracket,bracket]

theorem primitive_annihilates (m : Multiplier L) (h : C → B → Phase)
    (hh : ∀ t s a, m.value (t,s,a) = h s a + h t (a+d s) - h (s+t) a) :
    potentialCharacter (fun v => h v 0) ∈ annihilator (Bprim L) := by
  classical
  obtain ⟨f,hf⟩ := m.localTable
  let o (i : F) (s v : S i) := if s=0 ∨ v=0 then 0 else f ⟨i,s,v,0⟩
  have ho (i : F) : ∀ v, o i 0 v = 0 := by simp [o]
  have h0 (a : B) : h 0 a = 0 := by
    have e := hh 0 0 a
    simpa using e.symm
  apply (annihilates_primitive_iff L _).mpr
  refine ⟨onEdges h h0,fun i => onEdges (o i) (ho i),fun s v => ?_⟩
  have localSum : m.value (s,v,0) = ∑ i, o i (L.primitiveRes i s) (L.primitiveRes i v) := by
    rw [hf]
    simp only [triangleRead,map_sum]
    apply Finset.sum_congr rfl
    intro i _
    by_cases h' : L.primitiveRes i s=0 ∨ L.primitiveRes i v=0 <;> simp [h',o]
  have e := hh s v 0
  rw [localSum,zero_add] at e
  simp only [potentialCharacter_bracket,onEdges_edge]
  linear_combination (norm := abel) e

/-- The unbased primitive table extracted from a split transport law actually
descends to the previously formalized strict quotient. -/
theorem exists_primitive_character (m : Multiplier L) (hd : Function.Surjective d) :
    ∃ (h : C → B → Phase) (χ : TPrime L →ₗ[ℤ] Phase),
      (∀ t s a, m.value (t,s,a) = h s a + h t (a+d s) - h (s+t) a) ∧
      ∀ z : Zprim L, χ ((BprimInZprim L).mkQ z) = evaluate (fun v => h v 0) z.val.val := by
  obtain ⟨h,hh⟩ := exists_global_primitive m hd
  exact ⟨h,restrictCharacter _ _ ⟨_,primitive_annihilates L m h hh⟩,hh,fun _ => rfl⟩

end GeneralSphereT.Transport

