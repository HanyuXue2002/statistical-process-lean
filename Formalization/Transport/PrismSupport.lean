import Formalization.Transport.PrismChains

noncomputable section
namespace GeneralSphereT.Transport.Prism
open OpenDisk.PhaseDuality
variable {V Y : Type*}

inductive Stretch : List V → List V → Prop
  | nil : Stretch [] []
  | step {xs ys} (x : V) : Stretch xs ys → Stretch (x::xs) (x::ys)
  | repeatHead {x : V} {xs ys} : Stretch (x::xs) ys → Stretch (x::xs) (x::ys)

theorem Stretch.refl (xs : List V) : Stretch xs xs := by
  induction xs with
  | nil => exact .nil
  | cons x _ h => exact .step x h

theorem Stretch.mem {xs ys : List V} (h : Stretch xs ys) {v : V} (hv : v ∈ ys) : v ∈ xs := by
  induction h with
  | nil => simp at hv
  | step _ _ ih => simp only [List.mem_cons] at hv ⊢; exact hv.imp_right ih
  | repeatHead _ ih => rcases List.mem_cons.mp hv with rfl|e; exact List.mem_cons_self; exact ih e

theorem Stretch.pairwise [Preorder V] {xs ys : List V} (h : Stretch xs ys) (hs : xs.Pairwise (· ≤ ·)) :
    ys.Pairwise (· ≤ ·) := by
  induction h with
  | nil => simp
  | step x e ih =>
    obtain ⟨hx,ht⟩ := List.pairwise_cons.mp hs
    exact List.pairwise_cons.mpr ⟨fun y hy => hx y (e.mem hy),ih ht⟩
  | repeatHead e ih =>
    apply List.pairwise_cons.mpr
    refine ⟨fun y hy => ?_,ih hs⟩
    rcases List.mem_cons.mp (e.mem hy) with rfl|ht
    · exact le_rfl
    · exact (List.pairwise_cons.mp hs).1 _ ht

def walks (π : Y → V) (xs : List V) : Submodule ℤ (Chains Y) :=
  Submodule.span ℤ {z | ∃ ys, Stretch xs (ys.map π) ∧ z = gen ys}

theorem walk_generator {π : Y → V} {xs ys} (h : Stretch xs (ys.map π)) : gen ys ∈ walks π xs :=
  Submodule.subset_span ⟨ys,h,rfl⟩

private theorem walk_cons {π : Y → V} {xs xs' : List V} (y : Y)
    (e : ∀ vs, Stretch xs vs → Stretch xs' (π y::vs)) {z : Chains Y} (hz : z ∈ walks π xs) :
    cons y z ∈ walks π xs' := by
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨ys,h,rfl⟩ := hz
    rw [cons_gen]
    exact walk_generator (e _ h)
  | zero => simp
  | add x z _ _ hx hz => rw [map_add]; exact Submodule.add_mem _ hx hz
  | smul n x _ hx => rw [map_smul]; exact Submodule.smul_mem _ _ hx

theorem segment_walk {π : Y → V} {a b : V → Y} (ha : ∀ x, π (a x)=x) (hb : ∀ x, π (b x)=x)
    (xs : List V) : segmentList a b xs ∈ walks π xs := by
  induction xs with
  | nil => exact Submodule.zero_mem _
  | cons x xs ih =>
    apply Submodule.sub_mem
    · apply walk_cons (a x) (fun vs h => by rw [ha]; exact .repeatHead h)
      apply walk_generator
      simpa [List.map_map,Function.comp_def,hb] using Stretch.refl (x::xs)
    · apply walk_cons (a x) (fun vs h => by rw [ha]; exact .step x h) ih

theorem triangle_walk {π : Y → V} {a b c : V → Y} (ha : ∀ x, π (a x)=x) (hb : ∀ x, π (b x)=x)
    (hc : ∀ x, π (c x)=x) (xs : List V) : triangleList a b c xs ∈ walks π xs := by
  induction xs with
  | nil => exact Submodule.zero_mem _
  | cons x xs ih =>
    apply Submodule.add_mem
    · exact walk_cons (a x) (fun vs h => by rw [ha]; exact .repeatHead h) (segment_walk hb hc _)
    · exact walk_cons (a x) (fun vs h => by rw [ha]; exact .step x h) ih

theorem equal_on_walks {π : Y → V} {xs : List V} (f g : Chains Y →ₗ[ℤ] Phase)
    (h : ∀ ys, Stretch xs (ys.map π) → f (gen ys) = g (gen ys)) {p : Chains Y} (hp : p ∈ walks π xs) :
    f p = g p := by
  induction hp using Submodule.span_induction with
  | mem p hp => obtain ⟨ys,hw,rfl⟩ := hp; exact h _ hw
  | zero => simp
  | add _ _ _ _ hx hy => simp [hx,hy]
  | smul _ _ _ hx => simp [hx]

theorem vertices_segment {Z : Type*} (f : Y → Z) (a b : V → Y) (xs : List V) :
    vertices f (segmentList a b xs) = segmentList (f ∘ a) (f ∘ b) xs := by
  induction xs with
  | nil => simp [segmentList]
  | cons y ys ih => simp [segmentList,vertices_cons,ih,List.map_map]

theorem vertices_triangle {Z : Type*} (f : Y → Z) (a b c : V → Y) (xs : List V) :
    vertices f (triangleList a b c xs) = triangleList (f ∘ a) (f ∘ b) (f ∘ c) xs := by
  induction xs with
  | nil => simp [triangleList]
  | cons x xs ih => simp [triangleList,vertices_cons,vertices_segment,ih]

end GeneralSphereT.Transport.Prism

