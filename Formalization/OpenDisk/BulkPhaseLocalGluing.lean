import Formalization.OpenDisk.ConePhaseLocalLift

/-!
# Locality and the exact zero-slice inverse for a glued phase

A finite facet family is split into actual and cap facets. The actual region
`S` contains every actual facet, and the intersection of every cap facet with
`S` is contained in some actual facet. These are coordinate incidence facts,
not assumptions on phase tables. Under these hypotheses every local table
has a unique local actual/cap decomposition whose cap term vanishes on the
zero-new-coordinate slice. This supplies the locality part of the canonical
completion inverse without discarding constant phases.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace OpenDisk.BulkPhaseLocalGluing

open GeneralSphereT.PathAlgebra
open ConePhaseLocalLift

variable {ι G P A C : Type*} [LinearOrder ι] [AddCommGroup G] [AddCommGroup P]

/-- Keep precisely the coordinates in a region, putting zero elsewhere. -/
def project (S : Set ι) : Configuration ι G →+ Configuration ι G :=
  (coordinateExtension S).comp (coordinateRestriction S)

@[simp] theorem project_mem (S : Set ι) (c : Configuration ι G) {i : ι} (hi : i ∈ S) :
    project S c i = c i := by simp [project, hi]

@[simp] theorem project_not_mem (S : Set ι) (c : Configuration ι G) {i : ι} (hi : i ∉ S) :
    project S c i = 0 := by simp [project, hi]

@[simp] theorem project_idempotent (S : Set ι) (c : Configuration ι G) :
    project S (project S c) = project S c := by simp [project]

theorem project_single_mem (S : Set ι) {i : ι} (hi : i ∈ S) (g : G) :
    project S (Finsupp.single i g) = Finsupp.single i g := by
  change coordinateExtension S (coordinateRestriction S (Finsupp.single i g)) = _
  rw [coordinateRestriction_single_mem S hi]
  exact Finsupp.mapDomain_single

theorem project_single_not_mem (S : Set ι) {i : ι} (hi : i ∉ S) (g : G) :
    project S (Finsupp.single i g) = 0 := by
  simp [project, coordinateRestriction_single_not_mem S hi]

theorem local_refinement {F H : Type*} (facets : F → Set ι) (larger : H → Set ι)
    (h : ∀ ρ, ∃ σ, facets ρ ⊆ larger σ) {f : Configuration ι G → P}
    (hf : AnchoredLocal facets f) : AnchoredLocal larger f := by
  intro c hc
  apply hf c
  intro ρ hs
  obtain ⟨σ, hρσ⟩ := h ρ
  exact hc σ (fun i hi => hρσ (hs i hi))

/-- Truncating the input truncates each allowed facet by the same region. -/
theorem local_project_inter {F : Type*} (facets : F → Set ι) (S : Set ι)
    {f : Configuration ι G → P} (hf : AnchoredLocal facets f) :
    AnchoredLocal (fun ρ => facets ρ ∩ S) (fun c => f (project S c)) := by
  have hp := affine_pullback_local facets (fun ρ => facets ρ ∩ S) (project S) 0 hf
    (fun ρ i hi g => ?_)
  · simpa only [zero_add] using hp
  · by_cases hiS : i ∈ S
    · rw [project_single_mem S hiS]
      exact coordinateRestriction_single_not_mem _ (fun hiρ => hi ⟨hiρ, hiS⟩) g
    · rw [project_single_not_mem S hiS, map_zero]

theorem local_project {F : Type*} (facets : F → Set ι) (S : Set ι)
    {f : Configuration ι G → P} (hf : AnchoredLocal facets f) :
    AnchoredLocal facets (fun c => f (project S c)) :=
  local_refinement _ _ (fun ρ => ⟨ρ, Set.inter_subset_left⟩) (local_project_inter facets S hf)

/-- A phase local on facets inside a region is unchanged by deleting every
coordinate outside that region. -/
theorem local_eq_project {F : Type*} (facets : F → Set ι) (S : Set ι)
    (hinside : ∀ ρ, facets ρ ⊆ S) {f : Configuration ι G → P}
    (hf : AnchoredLocal facets f) (c : Configuration ι G) : f (project S c) = f c := by
  obtain ⟨g, hg⟩ := factors_restriction_of_anchored_zero S f (fun c hc =>
    hf c (fun ρ hρ => hc (fun i hi => hinside ρ (hρ i hi))))
  rw [hg, hg]
  congr 1
  simp [project]

variable [Fintype A] [Fintype C]

/-- Locality on the union of two finite facet families is exactly a sum of
one local phase on each side. -/
theorem local_union_iff (actual : A → Set ι) (cap : C → Set ι)
    (f : Configuration ι G → P) :
    AnchoredLocal (Sum.elim actual cap) f ↔
      ∃ φ χ : Configuration ι G → P,
        AnchoredLocal actual φ ∧ AnchoredLocal cap χ ∧ f = φ + χ := by
  constructor
  · intro hf
    obtain ⟨g, hg⟩ := hf.facetSum (Sum.elim actual cap) f
    let φ := fun c => ∑ ρ : A, g (Sum.inl ρ) (coordinateRestriction (actual ρ) c)
    let χ := fun c => ∑ ρ : C, g (Sum.inr ρ) (coordinateRestriction (cap ρ) c)
    refine ⟨φ, χ, FacetSum.anchoredLocal ⟨fun ρ => g (Sum.inl ρ), fun _ => rfl⟩,
      FacetSum.anchoredLocal ⟨fun ρ => g (Sum.inr ρ), fun _ => rfl⟩, ?_⟩
    funext c
    simpa [φ, χ, Fintype.sum_sum_type] using hg c
  · rintro ⟨φ, χ, hφ, hχ, rfl⟩
    exact (localFunctionSubgroup (Sum.elim actual cap) P).add_mem
      (local_refinement actual _ (fun ρ => ⟨Sum.inl ρ, Set.Subset.rfl⟩) hφ)
      (local_refinement cap _ (fun ρ => ⟨Sum.inr ρ, Set.Subset.rfl⟩) hχ)

def actualSlice (S : Set ι) (f : Configuration ι G → P) : Configuration ι G → P :=
  fun c => f (project S c)

def capSlice (S : Set ι) (f : Configuration ι G → P) : Configuration ι G → P :=
  fun c => f c - f (project S c)

@[simp] theorem capSlice_zero_slice (S : Set ι) (f : Configuration ι G → P)
    (c : Configuration ι G) : capSlice S f (project S c) = 0 := by
  simp [capSlice]

theorem normalized_split (S : Set ι) (f : Configuration ι G → P) :
    f = actualSlice S f + capSlice S f := by funext c; simp [actualSlice, capSlice]

/-- The normalized actual slice and cap remainder both retain their correct
side locality. The only boundary hypothesis is a checkable facet inclusion. -/
theorem normalized_slices_local (actual : A → Set ι) (cap : C → Set ι) (S : Set ι)
    (hactual : ∀ ρ, actual ρ ⊆ S)
    (hboundary : ∀ ρ, ∃ σ, cap ρ ∩ S ⊆ actual σ)
    {f : Configuration ι G → P} (hf : AnchoredLocal (Sum.elim actual cap) f) :
    AnchoredLocal actual (actualSlice S f) ∧ AnchoredLocal cap (capSlice S f) := by
  obtain ⟨φ, χ, hφ, hχ, rfl⟩ := (local_union_iff actual cap f).1 hf
  have hφS : ∀ c, φ (project S c) = φ c := local_eq_project actual S hactual hφ
  have hχS := local_project_inter cap S hχ
  have ha : actualSlice S (φ + χ) = φ + (fun c => χ (project S c)) := by
    funext c
    simp only [actualSlice, Pi.add_apply, hφS]
  have hc : capSlice S (φ + χ) = χ - (fun c => χ (project S c)) := by
    funext c
    simp only [capSlice, Pi.add_apply, Pi.sub_apply, hφS]
    abel
  rw [ha, hc]
  exact ⟨(localFunctionSubgroup actual P).add_mem hφ
    (local_refinement _ actual hboundary hχS),
    (localFunctionSubgroup cap P).sub_mem hχ (local_project cap S hχ)⟩

/-- The local completion inverse is exactly the zero slice. -/
theorem local_iff_normalized_slices (actual : A → Set ι) (cap : C → Set ι) (S : Set ι)
    (hactual : ∀ ρ, actual ρ ⊆ S)
    (hboundary : ∀ ρ, ∃ σ, cap ρ ∩ S ⊆ actual σ) (f : Configuration ι G → P) :
    AnchoredLocal (Sum.elim actual cap) f ↔
      AnchoredLocal actual (actualSlice S f) ∧ AnchoredLocal cap (capSlice S f) := by
  constructor
  · exact normalized_slices_local actual cap S hactual hboundary
  · intro h
    exact (local_union_iff actual cap f).2
      ⟨actualSlice S f, capSlice S f, h.1, h.2, normalized_split S f⟩

/-- Once the cap term vanishes on the zero slice, the local side split is
unique, including its constant phase. -/
theorem normalized_split_unique (actual : A → Set ι) (S : Set ι)
    (hactual : ∀ ρ, actual ρ ⊆ S) (f φ χ : Configuration ι G → P)
    (hφ : AnchoredLocal actual φ) (hzero : ∀ c, χ (project S c) = 0)
    (hsplit : f = φ + χ) : φ = actualSlice S f ∧ χ = capSlice S f := by
  have ha : φ = actualSlice S f := by
    funext c
    simp only [actualSlice, hsplit, Pi.add_apply, hzero, add_zero]
    exact (local_eq_project actual S hactual hφ c).symm
  refine ⟨ha, ?_⟩
  funext c
  change χ c = f c - actualSlice S f c
  rw [← ha, hsplit]
  simp

end OpenDisk.BulkPhaseLocalGluing
