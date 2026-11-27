import Formalization.Transport.Multiplier
import Mathlib.RingTheory.Finiteness.Finsupp

/-! Finite separating families of literal signed hopping words. -/
noncomputable section
open scoped BigOperators
namespace GeneralSphereT.Transport
open OpenDisk.PhaseDuality GeneralSphereT.PathAlgebra

variable {C B : Type*} [AddCommGroup C] [AddCommGroup B]
variable {F : Type*} [Fintype F] {S A : F → Type*}
variable [∀ i, AddCommGroup (S i)] [∀ i, AddCommGroup (A i)]
variable {d : C →+ B}
variable {L : FacetRestrictionData (Facet := F) (CAt := S) (BAt := A) d}

abbrev Word (C : Type*) := List (C × Bool)

/-- The prefix cochain and accumulated phase. An inverse reads its forward source. -/
def hop (c : Multiplier L) (a : B) (p : C × Phase) (step : C × Bool) : C × Phase :=
  if step.2 then (p.1 + step.1, p.2 + c.value (step.1,p.1,a))
  else (p.1 - step.1, p.2 - c.value (step.1,p.1-step.1,a))

def forward (v s t : C) : Word C :=
  [(v,true),(s,true),(t,true),(s+t,false),(v,false)]

def backward (v s t : C) : Word C :=
  [(v,true),(s+t,true),(t,false),(s,false),(v,false)]

theorem run_forward (c : Multiplier L) (v s t : C) (a : B) (p : Phase) :
    (forward v s t).foldl (hop c a) (0,p) = (0,p + c.value (t,s,a+d v)) := by
  have e : v+s+t-(s+t) = v := by abel
  have h := c.assoc t s v a
  simp only [forward, List.foldl_cons, List.foldl_nil, hop, ite_true, ite_false,
    Bool.false_eq_true, zero_add, Multiplier.zero_right, add_zero, e, sub_self, sub_zero]
  congr 1
  linear_combination (norm := abel) h

theorem run_backward (c : Multiplier L) (v s t : C) (a : B) (p : Phase) :
    (backward v s t).foldl (hop c a) (0,p) = (0,p - c.value (t,s,a+d v)) := by
  have e : v+(s+t)-t = v+s := by abel
  have h := c.assoc t s v a
  simp only [backward, List.foldl_cons, List.foldl_nil, hop, ite_true, ite_false,
    Bool.false_eq_true, zero_add, Multiplier.zero_right, add_zero, e,
    add_sub_cancel_right, sub_self, sub_zero]
  congr 1
  linear_combination (norm := abel) -h

def shiftTable (a : B) (f : Triangle C B → Phase) : Triangle C B → Phase :=
  fun x => f (x.1,x.2.1,a+x.2.2)

@[simp] theorem shiftTable_zero (f : Triangle C B → Phase) : shiftTable 0 f = f := by
  funext x
  rcases x with ⟨t,s,b⟩
  simp [shiftTable]

def Realizes (w : Word C) (x : Distribution (Triangle C B)) : Prop :=
  ∀ (c : Multiplier L) (a : B) (p : Phase),
    w.foldl (hop c a) (0,p) = (0,p + evaluate (shiftTable a c.value) x)

theorem realizes_append {u v : Word C} {x y : Distribution (Triangle C B)}
    (hu : Realizes (L:=L) u x) (hv : Realizes (L:=L) v y) :
    Realizes (L:=L) (u++v) (x+y) := by
  intro c a p
  rw [List.foldl_append,hu,hv,map_add,add_assoc]

theorem realized_integer_chain (hd : Function.Surjective d) (x : Distribution (Triangle C B)) :
    ∃ w : Word C, Realizes (L:=L) w x := by
  classical
  have zeroW : Realizes (L:=L) [] (0 : Distribution (Triangle C B)) := by
    intro c a p; simp
  have pos (k : Triangle C B) : ∃ w : Word C, Realizes (L:=L) w (Finsupp.single k 1) := by
    rcases k with ⟨t,s,b⟩
    obtain ⟨v,rfl⟩ := hd b
    exact ⟨forward v s t, fun c a p => by simpa [shiftTable] using run_forward c v s t a p⟩
  have neg (k : Triangle C B) : ∃ w : Word C, Realizes (L:=L) w (Finsupp.single k (-1)) := by
    rcases k with ⟨t,s,b⟩
    obtain ⟨v,rfl⟩ := hd b
    exact ⟨backward v s t, fun c a p => by simpa [shiftTable,sub_eq_add_neg] using run_backward c v s t a p⟩
  induction x using Finsupp.induction_linear with
  | zero => exact ⟨[],zeroW⟩
  | add x y hx hy =>
    obtain ⟨u,hu⟩ := hx
    obtain ⟨v,hv⟩ := hy
    exact ⟨_,realizes_append hu hv⟩
  | single k n =>
    induction n using Int.induction_on with
    | zero => simpa using (show ∃ w : Word C, Realizes (L:=L) w 0 from ⟨[],zeroW⟩)
    | succ n ih =>
      obtain ⟨u,hu⟩ := ih
      obtain ⟨v,hv⟩ := pos k
      exact ⟨_,by simpa [Finsupp.single_add] using realizes_append hu hv⟩
    | pred n ih =>
      obtain ⟨u,hu⟩ := ih
      obtain ⟨v,hv⟩ := neg k
      exact ⟨_,by simpa [sub_eq_add_neg,Finsupp.single_add] using realizes_append hu hv⟩

/-- Finite generators of the actual integer count kernel suffice for all pairs
of phase tables simultaneously. -/
theorem finite_tests [Finite C] [Finite B] :
    ∃ tests : Finset (Distribution (Triangle C B)),
    (∀ x ∈ tests, x ∈ LinearMap.ker (readBoundary L)) ∧
    ∀ c c', Equivalent L c c' ↔ ∀ x ∈ tests, evaluate c' x = evaluate c x := by
  classical
  obtain ⟨tests,hspan⟩ := IsNoetherian.noetherian (LinearMap.ker (readBoundary L))
  refine ⟨tests,fun x hx => hspan ▸ Submodule.subset_span hx,?_⟩
  intro c c'
  rw [equivalent_iff]
  constructor
  · intro h x hx; exact h x (hspan ▸ Submodule.subset_span hx)
  · intro h x hx
    have hle : Submodule.span ℤ (tests : Set _) ≤ LinearMap.ker (evaluate c' - evaluate c) :=
      Submodule.span_le.mpr (fun y hy => sub_eq_zero.mpr (h y hy))
    exact sub_eq_zero.mp (hle (hspan.symm ▸ hx))

/-- Shifting the initial curvature shifts every spatial read by the same local offset. -/
theorem read_shift (f : OneSlot S A → Phase) (s : C) (b a : B) :
    evaluate f (edgeRead L s (a+b)) =
    evaluate (fun k : OneSlot S A => f ⟨k.1,k.2.1,L.physicalRes k.1 a+k.2.2⟩)
      (edgeRead L s b) := by
  classical
  simp only [edgeRead,map_sum]
  apply Finset.sum_congr rfl
  intro i _
  split <;> simp_all

theorem equivalent_shift {c c' : Triangle C B → Phase} (h : Equivalent L c c') (a : B) :
    Equivalent L (shiftTable a c) (shiftTable a c') := by
  obtain ⟨f,hf⟩ := h
  refine ⟨fun k => f ⟨k.1,k.2.1,L.physicalRes k.1 a + k.2.2⟩, fun t s b => ?_⟩
  change c' (t,s,a+b)-c (t,s,a+b) = _
  rw [hf,add_assoc a b (d s)]
  rw [read_shift (L:=L) f s b a, read_shift (L:=L) f t (b+d s) a,
    read_shift (L:=L) f (s+t) b a]

def Statistical (w : Word C) : Prop :=
  (∀ (c : Multiplier L) (a : B), (w.foldl (hop c a) (0,0)).1 = 0) ∧
  ∀ (c c' : Multiplier L), Equivalent L c.value c'.value → ∀ a,
    (w.foldl (hop c a) (0,0)).2 = (w.foldl (hop c' a) (0,0)).2

/-- Quantifiers match the physical separation claim: one finite family of actual
words, invariant at *every* source, works simultaneously for every pair. -/
theorem finite_separating_words [Finite C] [Finite B] (hd : Function.Surjective d) :
    ∃ words : Finset (Word C), (∀ w ∈ words, Statistical (L:=L) w) ∧
    ∀ c c' : Multiplier L, Equivalent L c.value c'.value ↔
      ∀ w ∈ words, (w.foldl (hop c 0) (0,0)).2 = (w.foldl (hop c' 0) (0,0)).2 := by
  classical
  obtain ⟨xs,hxs,htest⟩ := finite_tests (L:=L)
  choose word hw using realized_integer_chain (L:=L) hd
  refine ⟨xs.image word, ?_, ?_⟩
  · intro w h
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp h
    refine ⟨fun c a => by rw [hw x c a], ?_⟩
    intro c c' he a
    rw [hw x c a,hw x c' a]
    simpa using ((equivalent_iff L _ _).mp (equivalent_shift he a) x (hxs x hx)).symm
  · intro c c'
    rw [htest]
    constructor
    · intro h w hw'
      obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hw'
      rw [hw x c 0,hw x c' 0]
      simpa only [shiftTable_zero,zero_add] using (h x hx).symm
    · intro h x hx
      have he := h (word x) (Finset.mem_image_of_mem word hx)
      rw [hw x c 0,hw x c' 0] at he
      simpa only [shiftTable_zero,zero_add] using he.symm

end GeneralSphereT.Transport

