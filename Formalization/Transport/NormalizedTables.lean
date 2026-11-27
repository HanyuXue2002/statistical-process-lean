import Formalization.Transport.Multiplier

/-! Normalization commutes with passing from a sum of local tables to a
global table.  Local decompositions are allowed to be nonunique. -/
noncomputable section
open scoped BigOperators
namespace GeneralSphereT.Transport
open GeneralSphereT.PathAlgebra OpenDisk.PhaseDuality
variable {C B F : Type*} [AddCommGroup C] [AddCommGroup B] [Fintype F]
variable {S A : F → Type*} [∀ i, AddCommGroup (S i)] [∀ i, AddCommGroup (A i)]
variable {d : C →+ B} (L : FacetRestrictionData (Facet:=F) (CAt:=S) (BAt:=A) d)

theorem normalized_two (p : Triangle C B → Phase)
    (h₁ : ∀ s a, p (0,s,a) = 0) (h₂ : ∀ t a, p (t,0,a) = 0)
    (f : ∀ i, S i → S i → A i → Phase)
    (hf : ∀ t s a, p (t,s,a) = ∑ i, f i (L.primitiveRes i t) (L.primitiveRes i s) (L.physicalRes i a)) :
    ∃ g : TwoSlot S A → Phase, ∀ x, p x = evaluate g (triangleRead L x) := by
  classical
  let g : TwoSlot S A → Phase := fun ⟨i,t,s,a⟩ => f i t s a - f i 0 s a - f i t 0 a + f i 0 0 a
  refine ⟨g,fun ⟨t,s,a⟩ => ?_⟩
  have e : evaluate g (triangleRead L (t,s,a)) =
      ∑ i, g ⟨i,L.primitiveRes i t,L.primitiveRes i s,L.physicalRes i a⟩ := by
    simp only [triangleRead,map_sum]
    apply Finset.sum_congr rfl
    intro i _
    by_cases h : L.primitiveRes i t=0 ∨ L.primitiveRes i s=0
    · rcases h with h|h <;> simp [h,g]
    · simp [h]
  rw [e]
  change _ = ∑ i, (f i _ _ _ - f i 0 _ _ - f i _ 0 _ + f i 0 0 _)
  rw [Finset.sum_add_distrib,Finset.sum_sub_distrib,Finset.sum_sub_distrib]
  have a₁ := hf 0 s a
  have a₂ := hf t 0 a
  have a₃ := hf 0 0 a
  simp only [h₁,h₂,map_zero] at a₁ a₂ a₃
  rw [← a₁,← a₂,← a₃,← hf]
  simp

theorem normalized_one (p : C → B → Phase) (h₀ : ∀ a, p 0 a = 0)
    (f : ∀ i, S i → A i → Phase)
    (hf : ∀ s a, p s a = ∑ i, f i (L.primitiveRes i s) (L.physicalRes i a)) :
    ∃ g : OneSlot S A → Phase, ∀ s a, p s a = evaluate g (edgeRead L s a) := by
  classical
  let g : OneSlot S A → Phase := fun ⟨i,s,a⟩ => f i s a - f i 0 a
  refine ⟨g,fun s a => ?_⟩
  have e : evaluate g (edgeRead L s a) =
      ∑ i, g ⟨i,L.primitiveRes i s,L.physicalRes i a⟩ := by
    simp only [edgeRead,map_sum]
    apply Finset.sum_congr rfl
    intro i _
    by_cases h : L.primitiveRes i s=0 <;> simp [h,g]
  rw [e]
  change _ = ∑ i, (f i _ _ - f i 0 _)
  rw [Finset.sum_sub_distrib,← hf]
  have a₁ := hf 0 a
  simp only [h₀,map_zero] at a₁
  rw [← a₁,sub_zero]

def curvature (h : C → B → Phase) (x : Triangle C B) : Phase :=
  h x.2.1 x.2.2 + h x.1 (x.2.2+d x.2.1) - h (x.2.1+x.1) x.2.2

theorem curvature_assoc (h : C → B → Phase) (r t s : C) (a : B) :
    curvature (d:=d) h (t,s,a) + curvature (d:=d) h (r,s+t,a) =
      curvature (d:=d) h (r,t,a+d s) + curvature (d:=d) h (t+r,s,a) := by
  simp only [curvature,map_add,add_assoc]
  abel

theorem curvature_zz (h : C → B → Phase) (z w : C) (a : B) (hz : d z=0) (hw : d w=0) :
    curvature (d:=d) h (w,z,a) = curvature (d:=d) h (z,w,a) := by
  simp [curvature,hz,hw,add_comm]

end GeneralSphereT.Transport

