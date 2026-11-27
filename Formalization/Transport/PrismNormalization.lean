import Formalization.Transport.PrismDegeneracy
import Formalization.Transport.PrismEvaluation

noncomputable section
namespace GeneralSphereT.Transport.Prism
open GeneralSphereT.StandardModels GeneralSphereT.SimplicialCochain OpenDisk.PhaseDuality
variable {V Y : Type*}

inductive Repeated : List Y → Prop
  | atStart (x : Y) (xs : List Y) : Repeated (x::x::xs)
  | nextHead (x : Y) {xs : List Y} : Repeated xs → Repeated (x::xs)

open CategoryTheory Opposite Simplicial

theorem Repeated.factor {ys : List Y} (h : Repeated ys) :
    ∃ (n : ℕ) (x : Fin (n+1) → Y) (i : Fin (n+1)), ys = List.ofFn (fun j => x (i.predAbove j)) := by
  induction h with
  | atStart y ys =>
    refine ⟨ys.length,(y::ys).get,0,?_⟩
    rw [List.ofFn_succ]
    simp only [Fin.predAbove_right_zero,Fin.predAbove_zero_succ,List.get_cons_zero]
    exact congrArg (List.cons y) (List.ofFn_get (y::ys)).symm
  | nextHead y _ ih =>
    obtain ⟨n,x,i,rfl⟩ := ih
    refine ⟨n+1,Fin.cons y x,i.succ,?_⟩
    conv_rhs => rw [List.ofFn_succ]
    simp [Fin.predAbove_right_zero]

def degenerates (Y : Type*) : Submodule ℤ (Chains Y) :=
  Submodule.span ℤ {p | ∃ ys, Repeated ys ∧ p=gen ys}

private theorem cons_repeated (y : Y) {z : Chains Y} (hz : z ∈ degenerates Y) : cons y z ∈ degenerates Y := by
  induction hz using Submodule.span_induction with
  | mem p hp =>
    obtain ⟨ys,h,rfl⟩ := hp
    rw [cons_gen]
    exact Submodule.subset_span ⟨_,Repeated.nextHead y h,rfl⟩
  | zero => simp
  | add _ _ _ _ ha hb => rw [map_add]; exact Submodule.add_mem _ ha hb
  | smul _ _ _ ha => rw [map_smul]; exact Submodule.smul_mem _ _ ha

private theorem twice_repeated (y : Y) (z : Chains Y) : cons y (cons y z) ∈ degenerates Y := by
  have h : (degenerates Y).mkQ.comp ((cons y).comp (cons y)) = 0 := by
    apply Finsupp.lhom_ext'
    intro xs
    apply LinearMap.ext_ring
    change (degenerates Y).mkQ (cons y (cons y (gen xs))) = 0
    rw [cons_gen,cons_gen,Submodule.mkQ_apply,Submodule.Quotient.mk_eq_zero]
    exact Submodule.subset_span ⟨_,Repeated.atStart y xs,rfl⟩
  exact (Submodule.Quotient.mk_eq_zero _).mp (LinearMap.congr_fun h z)

theorem segment_repeated (a : V → Y) (xs : List V) : segmentList a a xs ∈ degenerates Y := by
  induction xs with
  | nil => exact Submodule.zero_mem _
  | cons x xs ih =>
    change _ - _ ∈ degenerates Y
    apply Submodule.sub_mem _ _ (cons_repeated _ ih)
    rw [List.map_cons,← cons_gen]
    exact twice_repeated _ _

theorem triangle_repeated_left (a b : V → Y) (xs : List V) : triangleList a a b xs ∈ degenerates Y := by
  induction xs with
  | nil => exact Submodule.zero_mem _
  | cons x xs ih =>
    change _ + _ ∈ degenerates Y
    apply Submodule.add_mem _ _ (cons_repeated _ ih)
    rw [segmentList,map_sub]
    exact Submodule.sub_mem _ (twice_repeated _ _) (twice_repeated _ _)

theorem triangle_repeated_right (a b : V → Y) (xs : List V) : triangleList a b b xs ∈ degenerates Y := by
  induction xs with
  | nil => exact Submodule.zero_mem _
  | cons x xs ih => exact Submodule.add_mem _ (cons_repeated _ (segment_repeated _ _)) (cons_repeated _ ih)

variable {G : Type} [AddCommGroup G] {q p : ℕ}

def NormalizedOnEM (ω : EM G q (p+1) → Phase) : Prop :=
  ∀ (i : Fin (p+1)) (a : EM G q p), ω ((K (AddCommGrpCat.of G) q).σ i a) = 0

theorem pullCochain_degenerate (field : (Fin (q+1) → Y) → G)
    (hf : ∀ x, ¬Function.Injective x → field x=0)
    (ω : EM G (q+1) (p+1) → Phase) (hω : NormalizedOnEM ω) {z : Chains Y} (hz : z ∈ degenerates Y) :
    pullCochain field ω z=0 := by
  apply (show degenerates Y ≤ LinearMap.ker (pullCochain field ω) from ?_) hz
  apply Submodule.span_le.mpr
  rintro _ ⟨ys,h,rfl⟩
  obtain ⟨n,x,i,rfl⟩ := h.factor
  change pullCochain field ω (gen _) = 0
  by_cases hn : n=p
  · subst n
    simp only [pullCochain,gen,evaluate_single,one_zsmul,homogeneous_ofFn]
    exact (congrArg ω (classifyingValue_reparam field hf x i.predAboveOrderHom)).symm.trans (hω i _)
  · have h' : n+2 ≠ p+2 := by omega
    simp only [pullCochain,gen,evaluate_single,one_zsmul,homogeneous_ofFn_other _ _ h']

end GeneralSphereT.Transport.Prism

