import Formalization.OpenDisk.NormalFormTable

set_option linter.style.header false

/-!
# Marked tables and gauge invariance of operator locality

The elementary tables returned by the normal form satisfy the original
commutator-locality equations. Arbitrary diagonal phase conjugation preserves
these equations. Together these facts give both directions of the normal
form characterization, without restrictions on the potential.
-/

noncomputable section

open scoped BigOperators
open GeneralSphereT.PathAlgebra

namespace OpenDisk

variable {ι G A Facet : Type*} [LinearOrder ι] [AddCommGroup G] [AddCommGroup A]

private theorem iteratedDistributionDifference_zero_in_list
    (rs : List (Configuration ι G)) (hz : (0 : Configuration ι G) ∈ rs)
    (u : GeneralSphereT.PathAlgebra.Dist (Configuration ι G)) :
    iteratedDistributionDifference rs u = 0 := by
  have hd : distributionDifference (0 : Configuration ι G) = 0 := by
    ext c
    simp
  induction rs with
  | nil => simp at hz
  | cons r rs ih =>
      rcases List.mem_cons.mp hz with hr | hr
      · subst r
        simp [hd]
      · simp [ih hr]

/-- Anchored locality also controls arbitrary shifts whose restricted displacement vanishes. -/
theorem AnchoredLocal.iterated_restriction_zero (facets : Facet → Set ι)
    (f : Configuration ι G → A) (hf : AnchoredLocal facets f)
    (rs : List (Configuration ι G))
    (hrs : ∀ ρ, ∃ r ∈ rs, coordinateRestriction (facets ρ) r = 0)
    (c : Configuration ι G) : iteratedPhaseDifference rs f c = 0 := by
  rw [iteratedPhaseDifference_eq_pairing]
  apply (anchoredLocal_iff_annihilates_commonKernel facets f).mp hf
  rw [coordinateCommonRestrictionKernel, Submodule.mem_iInf]
  intro ρ
  rw [LinearMap.mem_ker, mapDist_iteratedDistributionDifference_apply]
  apply iteratedDistributionDifference_zero_in_list
  obtain ⟨r, hr, hz⟩ := hrs ρ
  exact List.mem_map.mpr ⟨r, hr, hz⟩

theorem elementaryStep_restriction_ne_zero (e : ElementaryLabel ι G) (S : Set ι)
    (he : e.val.1 ∈ S) : coordinateRestriction S (elementaryStep e) ≠ 0 := by
  rw [elementaryStep, coordinateRestriction_single_mem S he]
  exact Finsupp.single_ne_zero.mpr e.property

/-- Remove a visible marked operation from the no-common-facet list. -/
theorem noCommonFacetList_remove_mark (facets : Facet → Set ι)
    (e : ElementaryLabel ι G) (rs : List (Configuration ι G))
    (hfac : NoCommonFacetList (fun ρ => coordinateRestriction (G := G) (facets ρ))
      (elementaryStep e :: rs)) :
    ∀ ρ : {ρ : Facet // ∀ i ∈ ({e.val.1} : Finset ι), i ∈ facets ρ},
      ∃ r ∈ rs, coordinateRestriction (markedFacets facets {e.val.1} ρ) r = 0 := by
  intro ρ
  obtain ⟨r, hr, hz⟩ := (noCommonFacetList_iff _ _).mp hfac ρ.val
  rcases List.mem_cons.mp hr with he | hr
  · subst r
    exact (elementaryStep_restriction_ne_zero e (facets ρ.val)
      (ρ.property e.val.1 (Finset.mem_singleton_self _)) hz).elim
  · exact ⟨r, hr, hz⟩

theorem iteratedPhaseDifference_sub (rs : List (Configuration ι G))
    (f g : Configuration ι G → A) (c : Configuration ι G) :
    iteratedPhaseDifference rs (fun v => f v - g v) c =
      iteratedPhaseDifference rs f c - iteratedPhaseDifference rs g c := by
  simp only [iteratedPhaseDifference_eq_pairing, phasePairing_sub, LinearMap.sub_apply]

/-- Marked-local operation tables satisfy the full operator-locality axiom. -/
theorem tableOperatorLocal_of_marked (facets : Facet → Set ι)
    (T : ElementaryLabel ι G → Configuration ι G → A)
    (hT : ∀ e, MarkedLocal facets {e.val.1} (T e)) : TableOperatorLocal facets T := by
  intro e f rs c hfac
  have hswap : NoCommonFacetList
      (fun ρ => coordinateRestriction (G := G) (facets ρ))
      (elementaryStep f :: elementaryStep e :: rs) := by
    simpa only [noCommonFacetList_iff, List.mem_cons, or_comm, or_left_comm, or_assoc] using hfac
  have ht := AnchoredLocal.iterated_restriction_zero
    (markedFacets facets {f.val.1}) (T f) (hT f) (elementaryStep e :: rs)
    (noCommonFacetList_remove_mark facets f (elementaryStep e :: rs) hswap) c
  have hs := AnchoredLocal.iterated_restriction_zero
    (markedFacets facets {e.val.1}) (T e) (hT e) (elementaryStep f :: rs)
    (noCommonFacetList_remove_mark facets e (elementaryStep f :: rs) hfac) c
  rw [iteratedPhaseDifference_sub]
  change iteratedPhaseDifference (elementaryStep e :: rs) (T f) c -
    iteratedPhaseDifference (elementaryStep f :: rs) (T e) c = 0
  rw [ht, hs, sub_self]

/-- Conjugation of every operation by the same diagonal phase. -/
def gaugeTable (T : ElementaryLabel ι G → Configuration ι G → A)
    (β : Configuration ι G → A) : ElementaryLabel ι G → Configuration ι G → A := fun e c =>
  T e c + phaseDifference (elementaryStep e) β c

theorem gaugeTable_curvature (T : ElementaryLabel ι G → Configuration ι G → A)
    (β : Configuration ι G → A) (e f : ElementaryLabel ι G) :
    (fun v => phaseDifference (elementaryStep e) (gaugeTable T β f) v -
      phaseDifference (elementaryStep f) (gaugeTable T β e) v) =
    (fun v => phaseDifference (elementaryStep e) (T f) v -
      phaseDifference (elementaryStep f) (T e) v) := by
  funext v
  simp only [gaugeTable, phaseDifference]
  rw [show v + elementaryStep e + elementaryStep f =
    v + elementaryStep f + elementaryStep e by abel]
  abel

/-- Arbitrary diagonal conjugation preserves all nonface commutator equations. -/
theorem tableOperatorLocal_gauge_iff (facets : Facet → Set ι)
    (T : ElementaryLabel ι G → Configuration ι G → A) (β : Configuration ι G → A) :
    TableOperatorLocal facets (gaugeTable T β) ↔ TableOperatorLocal facets T := by
  unfold TableOperatorLocal
  simp only [gaugeTable_curvature]

/-- A table is operator-local exactly when it is a phase conjugate of marked-local operations. -/
theorem tableOperatorLocal_iff_normal_form (facets : Facet → Set ι)
    (hcover : ∀ i, ∃ ρ, i ∈ facets ρ)
    (T : ElementaryLabel ι G → Configuration ι G → A) :
    TableOperatorLocal facets T ↔
      ∃ (β : Configuration ι G → A) (O : ElementaryLabel ι G → Configuration ι G → A),
        (∀ e, MarkedLocal facets {e.val.1} (O e)) ∧ T = gaugeTable O β := by
  constructor
  · intro hT
    refine ⟨tableNormalPotential facets T, tableNormalResidual facets T,
      tableNormalResidual_markedLocal facets hcover T hT, ?_⟩
    funext e c
    exact (sub_add_cancel _ _).symm
  · rintro ⟨β, O, hO, rfl⟩
    exact (tableOperatorLocal_gauge_iff facets O β).mpr (tableOperatorLocal_of_marked facets O hO)

end OpenDisk
