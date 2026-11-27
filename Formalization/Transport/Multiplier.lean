import Formalization.OpenDisk.PhaseDuality
import Formalization.PrimitiveQuotient
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.RingTheory.Noetherian.Orzech

/-! Normalized local transport multipliers on the vacuum orbit. The later
move is the first argument, as in the transport algebra multiplication. -/
noncomputable section
open scoped BigOperators
namespace GeneralSphereT.Transport
open OpenDisk.PhaseDuality
open GeneralSphereT.PathAlgebra

variable {C B : Type*} [AddCommGroup C] [AddCommGroup B]
variable {F : Type*} [Fintype F] {S A : F → Type*}
variable [∀ i, AddCommGroup (S i)] [∀ i, AddCommGroup (A i)]
variable {d : C →+ B}
variable (L : FacetRestrictionData (Facet := F) (CAt := S) (BAt := A) d)

/-- The raw triangle labels, in multiplication order. -/
abbrev Triangle (C B : Type*) := C × C × B

abbrev OneSlot (S A : F → Type*) := Σ i, S i × A i
abbrev TwoSlot (S A : F → Type*) := Σ i, S i × S i × A i

def edgeRead (s : C) (a : B) : Distribution (OneSlot S A) := by
  classical
  exact ∑ i, if L.primitiveRes i s = 0 then 0 else
    Finsupp.single ⟨i,L.primitiveRes i s,L.physicalRes i a⟩ 1

def triangleRead (x : Triangle C B) : Distribution (TwoSlot S A) := by
  classical
  exact ∑ i, if L.primitiveRes i x.1 = 0 ∨ L.primitiveRes i x.2.1 = 0 then 0 else
    Finsupp.single ⟨i,L.primitiveRes i x.1,L.primitiveRes i x.2.1,L.physicalRes i x.2.2⟩ 1

def readBoundary : Distribution (Triangle C B) →ₗ[ℤ] Distribution (OneSlot S A) :=
  Finsupp.linearCombination ℤ fun x =>
    edgeRead L x.2.1 x.2.2 + edgeRead L x.1 (x.2.2 + d x.2.1) -
    edgeRead L (x.2.1 + x.1) x.2.2

/-- A single choice of one table for every facet, simultaneously at every input. -/
def Equivalent (c c' : Triangle C B → Phase) : Prop :=
  ∃ f : OneSlot S A → Phase, ∀ t s a, c' (t,s,a) - c (t,s,a) =
    evaluate f (edgeRead L s a) + evaluate f (edgeRead L t (a + d s)) -
    evaluate f (edgeRead L (s+t) a)

structure Multiplier where
  value : Triangle C B → Phase
  localTable : ∃ f : TwoSlot S A → Phase, ∀ x, value x = evaluate f (triangleRead L x)
  assoc : ∀ r t s a, value (t,s,a) + value (r,s+t,a) =
    value (r,t,a+d s) + value (t+r,s,a)
  zz : ∀ z w a, d z = 0 → d w = 0 → value (w,z,a) = value (z,w,a)

namespace Multiplier
variable {L}
@[simp] theorem zero_left (c : Multiplier L) (s : C) (a : B) :
    c.value (0,s,a) = 0 := by
  classical
  obtain ⟨f,h⟩ := c.localTable
  simp [h, triangleRead]

@[simp] theorem zero_right (c : Multiplier L) (s : C) (a : B) :
    c.value (s,0,a) = 0 := by
  classical
  obtain ⟨f,h⟩ := c.localTable
  simp [h, triangleRead]

theorem translated (c : Multiplier L) (r t s : C) (a : B) :
    c.value (t,s,a+d r) - c.value (t,s,a) =
    (c.value (s,r,a) - c.value (r,s,a)) +
    (c.value (t,r,a+d s) - c.value (r,t,a+d s)) -
    (c.value (s+t,r,a) - c.value (r,s+t,a)) := by
  have h₁ := c.assoc t s r a
  have h₂ := c.assoc t r s a
  have h₃ := c.assoc r t s a
  rw [add_comm r s] at h₁
  rw [add_comm r t] at h₂
  linear_combination (norm := abel) -h₁ + h₂ - h₃
end Multiplier

theorem equivalent_iff (c c' : Triangle C B → Phase) :
    Equivalent L c c' ↔ ∀ x ∈ LinearMap.ker (readBoundary L), evaluate c' x = evaluate c x := by
  classical
  let χ := evaluate c' - evaluate c
  have h := annihilates_kernel_iff (readBoundary L) χ
  constructor
  · rintro ⟨f,hf⟩ x hx
    have he : (evaluate f).comp (readBoundary L) = χ := by
      ext p
      rcases p with ⟨t,s,a⟩
      simpa [readBoundary,χ] using (hf t s a).symm
    exact sub_eq_zero.mp ((h.mpr ⟨evaluate f,he⟩) x hx)
  · intro hk
    obtain ⟨ψ,hψ⟩ := h.mp (fun x hx => sub_eq_zero.mpr (hk x hx))
    let f := phaseTableEquiv.symm ψ
    refine ⟨f,fun t s a => ?_⟩
    have hf : evaluate f = ψ := phaseTableEquiv.apply_symm_apply ψ
    have he := LinearMap.congr_fun hψ (Finsupp.single (t,s,a) 1)
    simpa [χ,readBoundary,hf] using he.symm

end GeneralSphereT.Transport

