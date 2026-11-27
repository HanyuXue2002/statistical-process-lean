import Formalization.OpenDisk.SymmetryLocality

/-!
# Locality of the cap primitive

This module develops the finite-difference argument used in the reverse
implication of Theorem 3.8. The differential into closed boundary cochains is
an actual additive map; the facet support condition on its elementary columns
is made explicit so it can be instantiated by the simplicial coboundary.
-/

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace OpenDisk.ConePhaseLocalLift

open GeneralSphereT.PathAlgebra

variable {ι κ G A P Facet : Type*} [LinearOrder ι] [LinearOrder κ]
  [AddCommGroup G] [AddCommGroup A] [AddCommGroup P]

local instance sumLinearOrder : LinearOrder (κ ⊕ ι) :=
  inferInstanceAs (LinearOrder (κ ⊕ₗ ι))

theorem iterated_zero (steps : List (Configuration ι G)) :
    iteratedPhaseDifference steps (0 : Configuration ι G → P) = 0 := by
  induction steps with
  | nil => rfl
  | cons s steps ih =>
      have h : phaseDifference s (0 : Configuration ι G → P) = 0 := by
        funext c; simp [phaseDifference]
      simpa only [iteratedPhaseDifference, h] using ih

theorem iterated_perm {steps rest : List (Configuration ι G)} (h : steps.Perm rest)
    (f : Configuration ι G → P) :
    iteratedPhaseDifference steps f = iteratedPhaseDifference rest f := by
  induction h generalizing f with
  | nil => rfl
  | cons s h ih => exact ih (phaseDifference s f)
  | swap s t steps =>
      have hc : phaseDifference t (phaseDifference s f) =
          phaseDifference s (phaseDifference t f) := by
        funext c
        exact difference_comm f s t c
      simp only [iteratedPhaseDifference, hc]
  | trans h h' ih ih' => exact (ih f).trans (ih' f)

theorem iterated_affine_pullback (h : Configuration κ G →+ Configuration ι G)
    (a : Configuration ι G) (steps : List (Configuration κ G))
    (f : Configuration ι G → P) (c : Configuration κ G) :
    iteratedPhaseDifference steps (fun x => f (a + h x)) c =
      iteratedPhaseDifference (steps.map h) f (a + h c) := by
  induction steps generalizing f with
  | nil => rfl
  | cons s steps ih =>
      have heq : phaseDifference s (fun x => f (a + h x)) =
          fun x => phaseDifference (h s) f (a + h x) := by
        funext x
        simp [phaseDifference, map_add, add_assoc]
      simpa only [iteratedPhaseDifference, List.map_cons, heq] using
        ih (phaseDifference (h s) f)

def activeFacets (facets : Facet → Set ι) (z : Configuration ι G) :
    {ρ : Facet // coordinateRestriction (facets ρ) z ≠ 0} → Set ι := fun ρ => facets ρ.val

/-- Intrinsic restriction locality makes a row local on exactly the facets
on which the closed translation is visible. The cover assumption rules out
unobservable global characters. -/
theorem active_row_local (facets : Facet → Set ι)
    (hcover : ∀ i, ∃ ρ, i ∈ facets ρ) (d : Configuration ι G →+ A)
    (F : SymmetryPhase d P) (hF : RestrictionSymmetryLocal facets d F) (z : d.ker) :
    AnchoredLocal (activeFacets facets (z : Configuration ι G)) (fun v => F z v) := by
  apply (differenceLocal_iff_anchoredLocal _ _).1
  by_cases hz : z = 0
  · subst z
    intro steps _ _ c
    have heq : (fun v => F 0 v) = (0 : Configuration ι G → P) := funext F.property.1
    rw [heq, iterated_zero]
    rfl
  · have hex : ∃ ρ, coordinateRestriction (facets ρ) (z : Configuration ι G) ≠ 0 := by
      by_contra! h
      apply hz
      apply Subtype.ext
      ext i
      obtain ⟨ρ, hi⟩ := hcover i
      exact congrArg (fun c : Configuration (facets ρ) G => c ⟨i, hi⟩) (h ρ)
    letI : Nonempty {ρ : Facet // coordinateRestriction (facets ρ) (z : Configuration ι G) ≠ 0} :=
      ⟨⟨hex.choose, hex.choose_spec⟩⟩
    rw [differenceLocal_iff_nonempty_lists]
    intro steps hne hactive hfac
    apply hF z steps hne hactive
    intro ρ
    by_cases hρ : coordinateRestriction (facets ρ) (z : Configuration ι G) = 0
    · exact Or.inl hρ
    · exact Or.inr (hfac ⟨ρ, hρ⟩)

def capParts : Configuration (κ ⊕ ι) G ≃+ Configuration κ G × Configuration ι G :=
  Finsupp.sumFinsuppAddEquivProdFinsupp

def newPart : Configuration (κ ⊕ ι) G →+ Configuration κ G :=
  (AddMonoidHom.fst _ _).comp capParts.toAddMonoidHom

def boundaryPart : Configuration (κ ⊕ ι) G →+ Configuration ι G :=
  (AddMonoidHom.snd _ _).comp capParts.toAddMonoidHom

@[simp] theorem newPart_apply (c : Configuration (κ ⊕ ι) G) (k : κ) :
    newPart c k = c (Sum.inl k) := rfl

@[simp] theorem boundaryPart_apply (c : Configuration (κ ⊕ ι) G) (i : ι) :
    boundaryPart c i = c (Sum.inr i) := rfl

@[simp] theorem newPart_single_new (k : κ) (g : G) :
    newPart (Finsupp.single (Sum.inl k : κ ⊕ ι) g) = Finsupp.single k g := by
  ext j
  simp [Finsupp.single_apply]

@[simp] theorem newPart_single_boundary (i : ι) (g : G) :
    newPart (Finsupp.single (Sum.inr i : κ ⊕ ι) g) = 0 := by
  ext j
  simp [Finsupp.single_apply]

@[simp] theorem boundaryPart_single_new (k : κ) (g : G) :
    boundaryPart (Finsupp.single (Sum.inl k : κ ⊕ ι) g) = 0 := by
  ext j
  simp [Finsupp.single_apply]

@[simp] theorem boundaryPart_single_boundary (i : ι) (g : G) :
    boundaryPart (Finsupp.single (Sum.inr i : κ ⊕ ι) g) = Finsupp.single i g := by
  ext j
  simp [Finsupp.single_apply]

def capFacets (facets : Facet → Set ι) (newFacets : Facet → Set κ) : Facet → Set (κ ⊕ ι) :=
  fun ρ => {s | Sum.elim (fun k => k ∈ newFacets ρ) (fun i => i ∈ facets ρ) s}

/-- A facet-compatible additive substitution preserves restriction locality. -/
theorem affine_pullback_local (facets : Facet → Set ι) (sourceFacets : Facet → Set κ)
    (h : Configuration κ G →+ Configuration ι G) (a : Configuration ι G)
    {f : Configuration ι G → P} (hf : AnchoredLocal facets f)
    (hcolumns : ∀ ρ k, k ∉ sourceFacets ρ → ∀ g,
      coordinateRestriction (facets ρ) (h (Finsupp.single k g)) = 0) :
    AnchoredLocal sourceFacets (fun c => f (a + h c)) := by
  apply (differenceLocal_iff_anchoredLocal _ _).1
  intro steps _ hfac c
  rw [iterated_affine_pullback]
  apply hf.arbitrary_differences
  intro ρ
  obtain ⟨p, hp, hpρ⟩ := hfac ρ
  refine ⟨h (Finsupp.single p.1 p.2), ?_, hcolumns ρ p.1 hpρ p.2⟩
  exact List.mem_map.mpr ⟨Finsupp.single p.1 p.2, List.mem_map.mpr ⟨p, hp, rfl⟩, rfl⟩

def newInclude : Configuration κ G →+ Configuration (κ ⊕ ι) G :=
  Finsupp.mapDomain.addMonoidHom Sum.inl

def boundaryInclude : Configuration ι G →+ Configuration (κ ⊕ ι) G :=
  Finsupp.mapDomain.addMonoidHom Sum.inr

@[simp] theorem newInclude_single (k : κ) (g : G) :
    newInclude (ι := ι) (Finsupp.single k g) = Finsupp.single (Sum.inl k) g :=
  Finsupp.mapDomain_single

@[simp] theorem boundaryInclude_single (i : ι) (g : G) :
    boundaryInclude (κ := κ) (Finsupp.single i g) = Finsupp.single (Sum.inr i) g :=
  Finsupp.mapDomain_single

@[simp] theorem newInclude_inl (u : Configuration κ G) (k : κ) :
    newInclude (ι := ι) u (Sum.inl k) = u k :=
  Finsupp.mapDomain_apply Sum.inl_injective u k

@[simp] theorem newInclude_inr (u : Configuration κ G) (i : ι) :
    newInclude (ι := ι) u (Sum.inr i) = 0 := by
  apply Finsupp.mapDomain_of_notMem_range
  simp

@[simp] theorem boundaryInclude_inl (v : Configuration ι G) (k : κ) :
    boundaryInclude (κ := κ) v (Sum.inl k) = 0 := by
  apply Finsupp.mapDomain_of_notMem_range
  simp

@[simp] theorem boundaryInclude_inr (v : Configuration ι G) (i : ι) :
    boundaryInclude (κ := κ) v (Sum.inr i) = v i :=
  Finsupp.mapDomain_apply Sum.inr_injective v i

@[simp] theorem newPart_newInclude (u : Configuration κ G) :
    newPart (newInclude (ι := ι) u) = u := by ext; simp

@[simp] theorem newPart_boundaryInclude (v : Configuration ι G) :
    newPart (boundaryInclude (κ := κ) v) = 0 := by ext; simp

@[simp] theorem boundaryPart_newInclude (u : Configuration κ G) :
    boundaryPart (newInclude (ι := ι) u) = 0 := by ext; simp

@[simp] theorem boundaryPart_boundaryInclude (v : Configuration ι G) :
    boundaryPart (boundaryInclude (κ := κ) v) = v := by ext; simp

theorem include_parts (c : Configuration (κ ⊕ ι) G) :
    newInclude (newPart c) + boundaryInclude (boundaryPart c) = c := by
  ext s
  cases s <;> simp

theorem boundary_list_of_no_new (steps : List ((κ ⊕ ι) × G))
    (h : ∀ k g, (Sum.inl k, g) ∉ steps) :
    ∃ bs : List (ι × G), steps = bs.map (fun p => (Sum.inr p.1, p.2)) := by
  induction steps with
  | nil => exact ⟨[], rfl⟩
  | cons p steps ih =>
      obtain ⟨s, g⟩ := p
      cases s with
      | inl k => exact (h k g List.mem_cons_self).elim
      | inr i =>
          obtain ⟨bs, hbs⟩ := ih (fun k g hk => h k g (List.mem_cons_of_mem _ hk))
          exact ⟨(i, g) :: bs, by simp only [List.map_cons, hbs]⟩

/-- A mixed-coordinate locality criterion. New-coordinate differences are
marked-local, while each fixed-new-coordinate boundary slice is local. -/
theorem local_of_new_differences_and_slices
    (facets : Facet → Set ι) (newFacets : Facet → Set κ)
    (f : Configuration (κ ⊕ ι) G → P)
    (hnew : ∀ k g, g ≠ 0 → MarkedLocal (capFacets facets newFacets) {Sum.inl k}
      (phaseDifference (Finsupp.single (Sum.inl k) g) f))
    (hslice : ∀ u : Configuration κ G, DifferenceLocal facets
      (fun v => f (newInclude u + boundaryInclude v))) :
    DifferenceLocal (capFacets facets newFacets) f := by
  classical
  intro steps hactive hfac c
  by_cases hn : ∃ k g, (Sum.inl k, g) ∈ steps
  · obtain ⟨k, g, hkg⟩ := hn
    let p : (κ ⊕ ι) × G := (Sum.inl k, g)
    obtain ⟨left, right, hsplit⟩ := List.mem_iff_append.mp hkg
    let rest := left ++ right
    have hperm : steps.Perm (p :: rest) := by rw [hsplit]; exact List.perm_middle
    rw [congrFun (iterated_perm (hperm.map (fun p => Finsupp.single p.1 p.2)) f) c]
    change iteratedPhaseDifference (rest.map (fun p => Finsupp.single p.1 p.2))
      (phaseDifference (Finsupp.single (Sum.inl k) g) f) c = 0
    apply (markedLocal_iff_differences _ _ _).1 (hnew k g (hactive _ hkg))
    · intro q hq
      exact hactive q (hperm.mem_iff.mpr (List.mem_cons_of_mem _ hq))
    · intro ρ
      obtain ⟨q, hq, hqρ⟩ := hfac ρ.val
      rcases List.mem_cons.mp (hperm.mem_iff.mp hq) with heq | hq
      · subst q
        exact (hqρ (ρ.property (Sum.inl k) (Finset.mem_singleton_self _))).elim
      · exact ⟨q, hq, hqρ⟩
  · obtain ⟨bs, rfl⟩ := boundary_list_of_no_new steps (by simpa only [not_exists] using hn)
    have hslicezero := hslice (newPart c) bs
      (fun p hp => hactive _ (List.mem_map.mpr ⟨p, hp, rfl⟩))
      (by
        intro ρ
        obtain ⟨q, hq, hqρ⟩ := hfac ρ
        obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hq
        exact ⟨p, hp, hqρ⟩) (boundaryPart c)
    rw [iterated_affine_pullback] at hslicezero
    simpa only [List.map_map, Function.comp_def, boundaryInclude_single, include_parts] using hslicezero

variable (d : Configuration ι G →+ A)

def capBase (D : Configuration κ G →+ d.ker) : Configuration (κ ⊕ ι) G →+ Configuration ι G :=
  boundaryPart - (d.ker.subtype.comp D).comp newPart

def capPhase (D : Configuration κ G →+ d.ker) (F : SymmetryPhase d P)
    (c : Configuration (κ ⊕ ι) G) : P := F (D (newPart c)) (capBase d D c)

theorem capPhase_new_difference (D : Configuration κ G →+ d.ker) (F : SymmetryPhase d P)
    (k : κ) (g : G) (c : Configuration (κ ⊕ ι) G) :
    phaseDifference (Finsupp.single (Sum.inl k) g) (capPhase d D F) c =
      F (D (Finsupp.single k g))
        (capBase d D (c + Finsupp.single (Sum.inl k) g)) := by
  let t : Configuration κ G := Finsupp.single k g
  let u := newPart c
  let v := boundaryPart c
  have h := F.property.2 (D t) (D u) (v - (D (u + t) : Configuration ι G))
  have hz : D (u + t) = D t + D u := by rw [map_add, add_comm]
  have hv : v - (D (u + t) : Configuration ι G) + (D t : Configuration ι G) =
      v - (D u : Configuration ι G) := by
    simp only [map_add, AddSubgroup.coe_add]
    abel
  rw [← hz, hv] at h
  have hn : newPart (c + Finsupp.single (Sum.inl k) g) = u + t := by
    simp only [map_add, newPart_single_new]
    rfl
  have hb : capBase d D (c + Finsupp.single (Sum.inl k) g) =
      v - (D (u + t) : Configuration ι G) := by
    change boundaryPart (c + Finsupp.single (Sum.inl k) g) -
      (D (newPart (c + Finsupp.single (Sum.inl k) g)) : Configuration ι G) = _
    rw [hn, map_add, boundaryPart_single_new, add_zero]
  change F (D (newPart (c + Finsupp.single (Sum.inl k) g)))
      (capBase d D (c + Finsupp.single (Sum.inl k) g)) -
    F (D (newPart c)) (capBase d D c) = _
  rw [hn, hb]
  change F (D (u + t)) (v - (D (u + t) : Configuration ι G)) -
    F (D u) (v - (D u : Configuration ι G)) =
      F (D t) (v - (D (u + t) : Configuration ι G))
  rw [h]
  abel

theorem capBase_single_invisible (facets : Facet → Set ι) (newFacets : Facet → Set κ)
    (D : Configuration κ G →+ d.ker)
    (hcolumns : ∀ ρ k, k ∉ newFacets ρ → ∀ g,
      coordinateRestriction (facets ρ) (D (Finsupp.single k g) : Configuration ι G) = 0)
    (ρ : Facet) (s : κ ⊕ ι) (hs : s ∉ capFacets facets newFacets ρ) (g : G) :
    coordinateRestriction (facets ρ) (capBase d D (Finsupp.single s g)) = 0 := by
  cases s with
  | inl k =>
      have hk : k ∉ newFacets ρ := hs
      change coordinateRestriction (facets ρ)
        (boundaryPart (Finsupp.single (Sum.inl k) g) -
          (D (newPart (Finsupp.single (Sum.inl k) g)) : Configuration ι G)) = 0
      rw [boundaryPart_single_new, newPart_single_new, zero_sub, map_neg, hcolumns ρ k hk g, neg_zero]
  | inr i =>
      have hi : i ∉ facets ρ := hs
      change coordinateRestriction (facets ρ)
        (boundaryPart (Finsupp.single (Sum.inr i) g) -
          (D (newPart (Finsupp.single (Sum.inr i) g)) : Configuration ι G)) = 0
      rw [boundaryPart_single_boundary, newPart_single_boundary, map_zero]
      simpa using coordinateRestriction_single_not_mem (facets ρ) hi g

/-- New-coordinate cap derivatives are local with their new carrier marked. -/
theorem capPhase_new_marked (facets : Facet → Set ι) (newFacets : Facet → Set κ)
    (hcover : ∀ i, ∃ ρ, i ∈ facets ρ)
    (D : Configuration κ G →+ d.ker)
    (hcolumns : ∀ ρ k, k ∉ newFacets ρ → ∀ g,
      coordinateRestriction (facets ρ) (D (Finsupp.single k g) : Configuration ι G) = 0)
    (F : SymmetryPhase d P) (hF : RestrictionSymmetryLocal facets d F) (k : κ) (g : G) :
    MarkedLocal (capFacets facets newFacets) {Sum.inl k}
      (phaseDifference (Finsupp.single (Sum.inl k) g) (capPhase d D F)) := by
  let z := D (Finsupp.single k g)
  have hf := active_row_local facets hcover d F hF z
  have hpull := affine_pullback_local (activeFacets facets (z : Configuration ι G))
    (fun ρ => capFacets facets newFacets ρ.val) (capBase d D)
    (capBase d D (Finsupp.single (Sum.inl k) g)) hf
    (fun ρ s hs g => capBase_single_invisible d facets newFacets D hcolumns ρ.val s hs g)
  have heq : phaseDifference (Finsupp.single (Sum.inl k) g) (capPhase d D F) =
      fun c => F z (capBase d D (Finsupp.single (Sum.inl k) g) + capBase d D c) := by
    funext c
    rw [capPhase_new_difference, map_add, add_comm]
  rw [heq]
  intro c hc
  apply hpull c
  intro ρ
  have hk : k ∈ newFacets ρ.val := by
    by_contra hk
    exact ρ.property (hcolumns ρ.val k hk g)
  exact hc ⟨ρ.val, by simpa [capFacets]
    using hk⟩

theorem capPhase_boundary_slice_local (facets : Facet → Set ι)
    (hcover : ∀ i, ∃ ρ, i ∈ facets ρ)
    (D : Configuration κ G →+ d.ker) (F : SymmetryPhase d P)
    (hF : RestrictionSymmetryLocal facets d F) (u : Configuration κ G) :
    DifferenceLocal facets (fun v => capPhase d D F (newInclude u + boundaryInclude v)) := by
  have ha := active_row_local facets hcover d F hF (D u)
  have hrow : AnchoredLocal facets (fun v => F (D u) v) :=
    fun c hc => ha c (fun ρ => hc ρ.val)
  have hpull := affine_pullback_local facets facets (AddMonoidHom.id (Configuration ι G))
    (-(D u : Configuration ι G)) hrow
    (fun ρ i hi g => coordinateRestriction_single_not_mem (facets ρ) hi g)
  have heq : (fun v => capPhase d D F (newInclude u + boundaryInclude v)) =
      fun v => F (D u) (-(D u : Configuration ι G) + v) := by
    funext v
    simp [capPhase, capBase, map_add, sub_eq_add_neg, add_comm]
  rw [heq]
  exact (differenceLocal_iff_anchoredLocal _ _).2 hpull

/-- The cone cap primitive is local, derived from intrinsic symmetry locality.
No local primitive or local lift is assumed. -/
theorem capPhase_local (facets : Facet → Set ι) (newFacets : Facet → Set κ)
    (hcover : ∀ i, ∃ ρ, i ∈ facets ρ)
    (D : Configuration κ G →+ d.ker)
    (hcolumns : ∀ ρ k, k ∉ newFacets ρ → ∀ g,
      coordinateRestriction (facets ρ) (D (Finsupp.single k g) : Configuration ι G) = 0)
    (F : SymmetryPhase d P) (hF : RestrictionSymmetryLocal facets d F) :
    DifferenceLocal (capFacets facets newFacets) (capPhase d D F) := by
  apply local_of_new_differences_and_slices
  · intro k g _
    exact capPhase_new_marked d facets newFacets hcover D hcolumns F hF k g
  · exact capPhase_boundary_slice_local d facets hcover D F hF

def closedCapStep (D : Configuration κ G →+ d.ker) (w : Configuration κ G) :
    Configuration (κ ⊕ ι) G := newInclude w + boundaryInclude (D w : Configuration ι G)

@[simp] theorem newPart_closedCapStep (D : Configuration κ G →+ d.ker) (w : Configuration κ G) :
    newPart (closedCapStep d D w) = w := by simp [closedCapStep]

@[simp] theorem boundaryPart_closedCapStep (D : Configuration κ G →+ d.ker)
    (w : Configuration κ G) :
    boundaryPart (closedCapStep d D w) = (D w : Configuration ι G) := by simp [closedCapStep]

@[simp] theorem capBase_closedCapStep (D : Configuration κ G →+ d.ker) (w : Configuration κ G) :
    capBase d D (closedCapStep d D w) = 0 := by simp [capBase]

/-- A closed cone translation has precisely the boundary symmetry phase. -/
theorem capPhase_closed_difference (D : Configuration κ G →+ d.ker) (F : SymmetryPhase d P)
    (w : Configuration κ G) (c : Configuration (κ ⊕ ι) G) :
    phaseDifference (closedCapStep d D w) (capPhase d D F) c = F (D w) (boundaryPart c) := by
  unfold phaseDifference capPhase
  simp only [map_add, capBase_closedCapStep, add_zero, newPart_closedCapStep]
  rw [F.property.2]
  have h : capBase d D c + (D (newPart c) : Configuration ι G) = boundaryPart c := by
    change boundaryPart c - (D (newPart c) : Configuration ι G) +
      (D (newPart c) : Configuration ι G) = _
    exact sub_add_cancel _ _
  rw [h]
  abel

/-- First-direction symmetry differences only use the closed cochain on the
facets containing that direction. This is derived from the intrinsic axiom. -/
theorem rowDifference_congr (facets : Facet → Set ι)
    (F : SymmetryPhase d P) (hF : RestrictionSymmetryLocal facets d F)
    (i : ι) (g : G) (hg : g ≠ 0) (z w : d.ker)
    (hzw : ∀ ρ, i ∈ facets ρ →
      coordinateRestriction (facets ρ) (z : Configuration ι G) =
        coordinateRestriction (facets ρ) (w : Configuration ι G)) (v : Configuration ι G) :
    difference (fun v => F z v) (Finsupp.single i g) v =
      difference (fun v => F w v) (Finsupp.single i g) v := by
  have hzero : ∀ c, difference (fun v => F (z - w) v) (Finsupp.single i g) c = 0 := by
    intro c
    apply hF (z - w) [(i, g)] (by simp) (by simp [hg])
      (fun ρ => ?_) c
    by_cases hi : i ∈ facets ρ
    · left
      simpa only [AddSubgroup.coe_sub, map_sub, hzw ρ hi, sub_self]
    · exact Or.inr ⟨(i, g), List.mem_cons_self, hi⟩
  have hsum : w + (z - w) = z := by abel
  have hrow : ∀ c, F z c = F w c + F (z - w) (c + w) := by
    intro c
    calc
      F z c = F (w + (z - w)) c := congrArg (fun t => F t c) hsum.symm
      _ = _ := F.property.2 w (z - w) c
  change F z (v + Finsupp.single i g) - F z v =
    F w (v + Finsupp.single i g) - F w v
  rw [hrow, hrow]
  have hzv := hzero (v + w)
  change F (z - w) (v + (w : Configuration ι G) + Finsupp.single i g) -
    F (z - w) (v + w) = 0 at hzv
  have heq : v + Finsupp.single i g + (w : Configuration ι G) =
      v + w + Finsupp.single i g := by abel
  rw [heq]
  rw [sub_eq_zero.mp hzv]
  abel

def capSection (h : Configuration ι G →+ Configuration κ G) :
    Configuration ι G →+ Configuration (κ ⊕ ι) G := newInclude.comp h + boundaryInclude

@[simp] theorem newPart_capSection (h : Configuration ι G →+ Configuration κ G)
    (v : Configuration ι G) : newPart (capSection h v) = h v := by simp [capSection]

@[simp] theorem boundaryPart_capSection (h : Configuration ι G →+ Configuration κ G)
    (v : Configuration ι G) : boundaryPart (capSection h v) = v := by simp [capSection]

def localLift (D : Configuration κ G →+ d.ker) (F : SymmetryPhase d P)
    (h : Configuration ι G →+ Configuration κ G) (i : ι) (g : G)
    (v : Configuration ι G) : P :=
  phaseDifference (Finsupp.single (Sum.inr i) g) (capPhase d D F) (capSection h v)

/-- Facetwise compatibility of the explicit local contraction makes the lift
marked-local. These hypotheses concern linear cochain maps, not phase lifts. -/
theorem localLift_marked (facets : Facet → Set ι) (newFacets : Facet → Set κ)
    (hcover : ∀ i, ∃ ρ, i ∈ facets ρ)
    (D : Configuration κ G →+ d.ker)
    (hcolumns : ∀ ρ k, k ∉ newFacets ρ → ∀ g,
      coordinateRestriction (facets ρ) (D (Finsupp.single k g) : Configuration ι G) = 0)
    (F : SymmetryPhase d P) (hF : RestrictionSymmetryLocal facets d F)
    (h : Configuration ι G →+ Configuration κ G) (i : ι) (g : G) (hg : g ≠ 0)
    (hsupport : ∀ ρ, i ∈ facets ρ → ∀ j, j ∉ facets ρ → ∀ a,
      coordinateRestriction (capFacets facets newFacets ρ)
        (capSection h (Finsupp.single j a)) = 0) :
    MarkedLocal facets {i} (localLift d D F h i g) := by
  have hmarked := (capPhase_local d facets newFacets hcover D hcolumns F hF).marked_difference
    (Sum.inr i) g hg
  let q := phaseDifference (Finsupp.single (Sum.inr i) g) (capPhase d D F)
  have hq : AnchoredLocal
      (fun ρ : {ρ : Facet // ∀ j ∈ ({i} : Finset ι), j ∈ facets ρ} =>
        capFacets facets newFacets ρ.val) q := by
    intro c hc
    apply hmarked c
    intro ρ
    exact hc ⟨ρ.val, by
      intro j hj
      have hij : j = i := Finset.mem_singleton.mp hj
      subst j
      exact ρ.property (Sum.inr i) (Finset.mem_singleton_self _)⟩
  have hpull := affine_pullback_local
    (fun ρ : {ρ : Facet // ∀ j ∈ ({i} : Finset ι), j ∈ facets ρ} =>
      capFacets facets newFacets ρ.val)
    (markedFacets facets {i}) (capSection h) 0 hq
    (fun ρ j hj a => hsupport ρ.val (ρ.property i (Finset.mem_singleton_self _)) j hj a)
  change AnchoredLocal (markedFacets facets {i}) (fun c => q (capSection h c))
  simpa only [zero_add] using hpull

theorem boundaryInclude_invisible (facets : Facet → Set ι) (newFacets : Facet → Set κ)
    (ρ : Facet) (v : Configuration ι G) (hv : coordinateRestriction (facets ρ) v = 0) :
    coordinateRestriction (capFacets facets newFacets ρ) (boundaryInclude v) = 0 := by
  ext s
  rcases s with ⟨s, hs⟩
  cases s with
  | inl k =>
      change boundaryInclude v (Sum.inl k) = 0
      simp
  | inr i =>
      have hi : i ∈ facets ρ := hs
      have h := congrArg (fun c => c ⟨i, hi⟩) hv
      change v i = 0 at h
      change boundaryInclude v (Sum.inr i) = 0
      simpa using h

/-- The explicit cap derivative matches the symmetry table whenever the
linear cochain contraction reproduces a closed cochain on the marked star.
The hypothesis is a linear contraction identity, not a phase lifting axiom. -/
theorem localLift_matches (facets : Facet → Set ι) (newFacets : Facet → Set κ)
    (hcover : ∀ i, ∃ ρ, i ∈ facets ρ)
    (D : Configuration κ G →+ d.ker)
    (hcolumns : ∀ ρ k, k ∉ newFacets ρ → ∀ g,
      coordinateRestriction (facets ρ) (D (Finsupp.single k g) : Configuration ι G) = 0)
    (F : SymmetryPhase d P) (hF : RestrictionSymmetryLocal facets d F)
    (h : Configuration ι G →+ Configuration κ G) (i : ι) (g : G) (hg : g ≠ 0)
    (hcontracts : ∀ (z : d.ker) ρ, i ∈ facets ρ →
      coordinateRestriction (facets ρ) (D (h (z : Configuration ι G)) : Configuration ι G) =
        coordinateRestriction (facets ρ) (z : Configuration ι G))
    (z : d.ker) (v : Configuration ι G) :
    difference (localLift d D F h i g) (z : Configuration ι G) v =
      difference (fun v => F z v) (Finsupp.single i g) v := by
  let q := phaseDifference (Finsupp.single (Sum.inr i) g) (capPhase d D F)
  let w := h (z : Configuration ι G)
  let y := closedCapStep d D w
  let c := capSection h v
  let δ := boundaryInclude (κ := κ) ((z : Configuration ι G) - (D w : Configuration ι G))
  have hq : MarkedLocal (capFacets facets newFacets) {Sum.inr i} q :=
    (capPhase_local d facets newFacets hcover D hcolumns F hF).marked_difference
      (Sum.inr i) g hg
  have hδ : ∀ ρ : {ρ : Facet // ∀ j ∈ ({Sum.inr i} : Finset (κ ⊕ ι)),
      j ∈ capFacets facets newFacets ρ},
      coordinateRestriction (capFacets facets newFacets ρ.val) δ = 0 := by
    intro ρ
    apply boundaryInclude_invisible
    rw [map_sub, hcontracts z ρ.val (ρ.property (Sum.inr i) (Finset.mem_singleton_self _)), sub_self]
  have hshift : capSection h (z : Configuration ι G) = y + δ := by
    change newInclude (h (z : Configuration ι G)) + boundaryInclude (z : Configuration ι G) =
      (newInclude w + boundaryInclude (D w : Configuration ι G)) +
        boundaryInclude ((z : Configuration ι G) - (D w : Configuration ι G))
    rw [map_sub]
    dsimp [w]
    abel
  have hinv : q (c + y + δ) = q (c + y) := by
    have hzero := hq.arbitrary_differences [δ]
      (fun ρ => ⟨δ, List.mem_cons_self, hδ ρ⟩) (c + y)
    exact sub_eq_zero.mp hzero
  have hcap : difference (capPhase d D F) y =
      fun x => F (D w) (boundaryPart x) := by
    funext x
    exact capPhase_closed_difference d D F w x
  calc
    difference (localLift d D F h i g) (z : Configuration ι G) v =
        difference q y c := by
      change q (capSection h (v + (z : Configuration ι G))) - q c = q (c + y) - q c
      rw [map_add, hshift, ← add_assoc]
      exact congrArg (fun t => t - q c) hinv
    _ = difference (fun x => F (D w) (boundaryPart x))
        (Finsupp.single (Sum.inr i) g) c := by
      change difference (difference (capPhase d D F) (Finsupp.single (Sum.inr i) g)) y c = _
      rw [difference_comm, hcap]
    _ = difference (fun x => F (D w) x) (Finsupp.single i g) v := by
      simp only [difference, map_add, boundaryPart_single_boundary, c, boundaryPart_capSection]
    _ = difference (fun x => F z x) (Finsupp.single i g) v :=
      rowDifference_congr d facets F hF i g hg (D w) z (hcontracts z) v

/-- The local lift theorem with explicit cochain contraction data. Both the
phase and its locality/matching proofs are constructed from that data. -/
theorem exists_localLift (facets : Facet → Set ι) (newFacets : Facet → Set κ)
    (hcover : ∀ i, ∃ ρ, i ∈ facets ρ)
    (D : Configuration κ G →+ d.ker)
    (hcolumns : ∀ ρ k, k ∉ newFacets ρ → ∀ g,
      coordinateRestriction (facets ρ) (D (Finsupp.single k g) : Configuration ι G) = 0)
    (F : SymmetryPhase d P) (hF : RestrictionSymmetryLocal facets d F)
    (h : Configuration ι G →+ Configuration κ G) (i : ι) (g : G) (hg : g ≠ 0)
    (hsupport : ∀ ρ, i ∈ facets ρ → ∀ j, j ∉ facets ρ → ∀ a,
      coordinateRestriction (capFacets facets newFacets ρ)
        (capSection h (Finsupp.single j a)) = 0)
    (hcontracts : ∀ (z : d.ker) ρ, i ∈ facets ρ →
      coordinateRestriction (facets ρ) (D (h (z : Configuration ι G)) : Configuration ι G) =
        coordinateRestriction (facets ρ) (z : Configuration ι G)) :
    ∃ L : Configuration ι G → P, MarkedLocal facets {i} L ∧
      ∀ (z : d.ker) v, difference L z v = difference (fun v => F z v) (Finsupp.single i g) v :=
  ⟨localLift d D F h i g,
    localLift_marked d facets newFacets hcover D hcolumns F hF h i g hg hsupport,
    localLift_matches d facets newFacets hcover D hcolumns F hF h i g hg hcontracts⟩

end OpenDisk.ConePhaseLocalLift
