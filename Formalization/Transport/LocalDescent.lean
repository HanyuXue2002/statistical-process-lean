import Formalization.Transport.Multiplier
import Formalization.RelativePrimitiveSection

/-! Descent of a jointly local table from primitive bases to physical configurations.
A difference in one time coordinate only sees facets containing that coordinate.
The star-adapted primitive section therefore works for every summand in that difference. -/
noncomputable section
open scoped BigOperators
namespace GeneralSphereT.Transport
open GeneralSphereT.PathAlgebra OpenDisk.PhaseDuality
variable {I G B F : Type*} [LinearOrder I] [Fintype I] [AddCommGroup G] [AddCommGroup B]
variable [Fintype F] (facets : F → Set I)
variable {A : F → Type*} [∀ i, AddCommGroup (A i)]
variable {d : Configuration I G →+ B}
variable (L : FacetRestrictionData (Facet:=F) (CAt:=fun i => Configuration (facets i) G) (BAt:=A) d)
variable (D : RelativePrimitiveSectionData facets L)

private def truncate {J : Type*} (j : J → I) (u : Finset I) (s : Configuration J G) :
    Configuration J G := by
  classical
  exact s.filter (fun k => j k ∈ u)

omit [Fintype I] [Fintype F] in
private theorem truncate_restrict (i : F) (u : Finset I) (s : Configuration I G) :
    coordinateRestriction (facets i) (truncate id u s) =
      truncate Subtype.val u (coordinateRestriction (facets i) s) := by
  classical
  ext k
  simp [truncate,Finsupp.filter_apply]

omit [Fintype I] [Fintype F] in
private theorem truncate_insert_outside (i : F) (j : I) (hj : j ∉ facets i) (u : Finset I)
    (s : Configuration (facets i) G) :
    truncate Subtype.val (insert j u) s = truncate Subtype.val u s := by
  classical
  ext k
  have hk : k.val ≠ j := fun e => hj (e ▸ k.property)
  simp [truncate,Finsupp.filter_apply,hk]

include D in
/-- Extra time parameters can have arbitrary types and arbitrary local reads.
The descent preserves their joint locality with the marked time variable. -/
theorem joint_local_descent {Y : Type*} {Yi : F → Type*} (ys : ∀ i, Y → Yi i)
    (h : Configuration I G → Y → B → Phase) (h0 : ∀ y a, h 0 y a = 0)
    (f : ∀ i, Configuration (facets i) G → Yi i → Configuration (facets i) G → Phase)
    (hf : ∀ s y v, h s y (d v) = ∑ i, f i (coordinateRestriction (facets i) s)
      (ys i y) (coordinateRestriction (facets i) v)) :
    ∃ g : ∀ i, Configuration (facets i) G → Yi i → A i → Phase,
      ∀ s y a, h s y a = ∑ i, g i (coordinateRestriction (facets i) s) (ys i y) (L.physicalRes i a) := by
  classical
  let loc (u : Finset I) := ∃ g : ∀ i, Configuration (facets i) G → Yi i → A i → Phase,
    ∀ s y a, h (truncate id u s) y a =
      ∑ i, g i (coordinateRestriction (facets i) s) (ys i y) (L.physicalRes i a)
  have every (u : Finset I) : loc u := by
    induction u using Finset.induction_on with
    | empty =>
      refine ⟨fun _ _ _ _ => 0,fun s y a => ?_⟩
      have hz : truncate id (∅ : Finset I) s = 0 := by
        ext k
        simp [truncate]
      simp [hz,h0]
    | @insert j u _ ih =>
      obtain ⟨g,hg⟩ := ih
      let diff (i : F) (s : Configuration (facets i) G) (y : Yi i) (a : A i) :=
        if hj : j ∈ facets i then
          f i (truncate Subtype.val (insert j u) s) y (D.localPrimitive i ⟨j,hj⟩ a) -
          f i (truncate Subtype.val u s) y (D.localPrimitive i ⟨j,hj⟩ a)
        else 0
      refine ⟨fun i s y a => g i s y a + diff i s y a, fun s y a => ?_⟩
      rw [Finset.sum_add_distrib,← hg]
      apply eq_add_of_sub_eq'
      let v := D.globalPrimitive j a
      have hd : d v = a := D.map_globalPrimitive j a
      rw [← hd, hf, hf, ← Finset.sum_sub_distrib, hd]
      apply Finset.sum_congr rfl
      intro i _
      rw [truncate_restrict,truncate_restrict]
      by_cases hj : j ∈ facets i
      · simp only [diff,dif_pos hj,v,D.restrict_globalPrimitive i j hj]
      · simp [diff,hj,truncate_insert_outside facets i j hj]
  obtain ⟨g,hg⟩ := every Finset.univ
  refine ⟨g,fun s y a => ?_⟩
  have hu : truncate id Finset.univ s = s := by ext k; simp [truncate]
  simpa only [hu] using hg s y a

end GeneralSphereT.Transport

