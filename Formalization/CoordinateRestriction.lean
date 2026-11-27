import Formalization.Subdivision

set_option linter.style.header false

/-!
# Coordinate restriction and ordered paths

Restriction changes the coordinate type from `ι` to the subtype cut out by a
set `S`.  The subtype inherits the ambient order, so restriction truly deletes
coordinates without choosing a new ordering.  This proves the strict
restriction compatibility asserted after (2.14) and for `p_*` after (2.16).
-/

noncomputable section

open scoped BigOperators

namespace GeneralSphereT.PathAlgebra

variable {ι G : Type*} [LinearOrder ι] [AddCommGroup G]

local instance instDecidableSetMembership (S : Set ι) :
    DecidablePred (fun i => i ∈ S) :=
  Classical.decPred _

/-- Delete the coordinates outside `S`, retaining the ambient order on `S`. -/
def coordinateRestriction (S : Set ι) :
    Configuration ι G →+ Configuration S G :=
  Finsupp.subtypeDomainAddMonoidHom

omit [LinearOrder ι] in
@[simp]
theorem coordinateRestriction_apply (S : Set ι)
    (r : Configuration ι G) (i : S) :
    coordinateRestriction S r i = r i.1 :=
  rfl

omit [LinearOrder ι] in
@[simp]
theorem support_coordinateRestriction (S : Set ι)
    (r : Configuration ι G) :
    (coordinateRestriction S r).support =
      r.support.subtype (fun i => i ∈ S) := by
  classical
  exact Finsupp.support_subtypeDomain

@[simp]
theorem coordinateRestriction_single_mem (S : Set ι) {i : ι}
    (hi : i ∈ S) (g : G) :
    coordinateRestriction S (Finsupp.single i g) =
      Finsupp.single ⟨i, hi⟩ g := by
  classical
  change (Finsupp.single i g).subtypeDomain (fun j => j ∈ S) =
    Finsupp.single ⟨i, hi⟩ g
  ext j
  simp [Finsupp.single_apply, Subtype.ext_iff]

omit [LinearOrder ι] in
@[simp]
theorem coordinateRestriction_single_not_mem (S : Set ι) {i : ι}
    (hi : i ∉ S) (g : G) :
    coordinateRestriction S (Finsupp.single i g) = 0 := by
  classical
  change (Finsupp.single i g).subtypeDomain (fun j => j ∈ S) = 0
  ext j
  have hij : i ≠ j.1 := by
    intro hij
    apply hi
    exact hij.symm ▸ j.2
  simp [hij]

/-- `coordinatePrefix` is truncation below the chosen coordinate. -/
theorem coordinatePrefix_eq_filter (r : Configuration ι G) (i : ι) :
    coordinatePrefix r i = r.filter (fun j => j < i) := by
  classical
  simpa only [coordinatePrefix, prefixSum] using
    (Finsupp.filter_eq_sum (fun j => j < i) r).symm

@[simp]
theorem coordinatePrefix_apply (r : Configuration ι G) (i j : ι) :
    coordinatePrefix r i j = if j < i then r j else 0 := by
  classical
  simp [coordinatePrefix_eq_filter, Finsupp.filter_apply]

/-- Restriction preserves prefixes because the subtype order is inherited. -/
theorem coordinateRestriction_coordinatePrefix (S : Set ι)
    (r : Configuration ι G) (i : S) :
    coordinateRestriction S (coordinatePrefix r i.1) =
      coordinatePrefix (coordinateRestriction S r) i := by
  classical
  ext j
  simp [coordinatePrefix_apply]

/-- The target step associated with an ambient coordinate; zero off `S`. -/
private noncomputable def restrictedOrderedStep (S : Set ι)
    (r x : Configuration ι G) (i : ι) :
    Path (Configuration S G) (Configuration S G) :=
  if hi : i ∈ S then
    edge (Finsupp.single ⟨i, hi⟩ (r i))
      (coordinateRestriction S x +
        coordinatePrefix (coordinateRestriction S r) ⟨i, hi⟩)
  else
    0

/-- Coordinate restriction strictly commutes with the ordered path. -/
theorem mapPath_orderedPath_coordinateRestriction (S : Set ι)
    (r x : Configuration ι G) :
    mapPath (coordinateRestriction S) (coordinateRestriction S)
        (orderedPath r x) =
      orderedPath (coordinateRestriction S r) (coordinateRestriction S x) := by
  classical
  have hsource :
      mapPath (coordinateRestriction S) (coordinateRestriction S)
          (orderedPath r x) =
        ∑ i ∈ r.support, restrictedOrderedStep S r x i := by
    rw [orderedPath, map_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [mapPath_edge]
    by_cases hiS : i ∈ S
    · rw [coordinateRestriction_single_mem S hiS]
      rw [map_add]
      rw [coordinateRestriction_coordinatePrefix S r ⟨i, hiS⟩]
      simp [restrictedOrderedStep, hiS]
    · simp [restrictedOrderedStep, hiS]
  have htarget :
      orderedPath (coordinateRestriction S r) (coordinateRestriction S x) =
        ∑ i ∈ r.support.subtype (fun j => j ∈ S),
          restrictedOrderedStep S r x i.1 := by
    rw [orderedPath, support_coordinateRestriction]
    apply Finset.sum_congr rfl
    intro i hi
    simp [restrictedOrderedStep, i.2]
  have hsubtype :
      (∑ i ∈ r.support.subtype (fun j => j ∈ S),
          restrictedOrderedStep S r x i.1) =
        ∑ i ∈ r.support.filter (fun j => j ∈ S),
          restrictedOrderedStep S r x i := by
    exact Finset.sum_subtype_eq_sum_filter
      (s := r.support) (p := fun j => j ∈ S)
      (f := restrictedOrderedStep S r x)
  have hfilter :
      (∑ i ∈ r.support.filter (fun j => j ∈ S),
          restrictedOrderedStep S r x i) =
        ∑ i ∈ r.support, restrictedOrderedStep S r x i := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro i hiSupport hiFilter
    have hiS : i ∉ S := by
      intro hiS
      exact hiFilter (Finset.mem_filter.mpr ⟨hiSupport, hiS⟩)
    simp [restrictedOrderedStep, hiS]
  rw [hsource, htarget, hsubtype, hfilter]

/-- Ordered subdivision is natural under restriction before the path quotient. -/
theorem rawSubdivision_coordinateRestriction (S : Set ι) :
    (mapPath (coordinateRestriction S) (coordinateRestriction S)).comp
        (rawSubdivision (ι := ι) (G := G)) =
      (rawSubdivision (ι := S) (G := G)).comp
        (rawMapPath (coordinateRestriction S) (coordinateRestriction S)) := by
  ext p
  rcases p with ⟨r, x⟩
  change
    mapPath (coordinateRestriction S) (coordinateRestriction S)
        (rawSubdivision (rawEdge r x)) =
      rawSubdivision
        (rawMapPath (coordinateRestriction S) (coordinateRestriction S)
          (rawEdge r x))
  simp [mapPath_orderedPath_coordinateRestriction]

/-- The strict restriction naturality of subdivision on path classes. -/
theorem subdivision_coordinateRestriction (S : Set ι) :
    (mapPath (coordinateRestriction S) (coordinateRestriction S)).comp
        (subdivision (ι := ι) (G := G)) =
      (subdivision (ι := S) (G := G)).comp
        (mapPath (coordinateRestriction S) (coordinateRestriction S)) := by
  apply LinearMap.ext
  intro p
  refine Submodule.Quotient.induction_on
    (p := zeroIncrement (Configuration ι G) (Configuration ι G)) p ?_
  intro q
  change
    mapPath (coordinateRestriction S) (coordinateRestriction S)
        (rawSubdivision q) =
      rawSubdivision
        (rawMapPath (coordinateRestriction S) (coordinateRestriction S) q)
  exact LinearMap.congr_fun (rawSubdivision_coordinateRestriction S) q

/-- Naturality of the unreduced canonical path under coordinate restriction. -/
theorem rawCanonicalPath_coordinateRestriction (S : Set ι) :
    (mapPath (coordinateRestriction S) (coordinateRestriction S)).comp
        (rawCanonicalPath (ι := ι) (G := G)) =
      (rawCanonicalPath (ι := S) (G := G)).comp
        (mapDist (coordinateRestriction S)) := by
  ext c
  simp [mapPath_orderedPath_coordinateRestriction]

/-- Naturality of the canonical path on augmentation-zero distributions. -/
theorem canonicalPath_coordinateRestriction (S : Set ι) :
    (mapPath (coordinateRestriction S) (coordinateRestriction S)).comp
        (canonicalPath (ι := ι) (G := G)) =
      (canonicalPath (ι := S) (G := G)).comp
        (mapRedDist (coordinateRestriction S)) := by
  apply LinearMap.ext
  intro u
  change
    mapPath (coordinateRestriction S) (coordinateRestriction S)
        (rawCanonicalPath u.1) =
      rawCanonicalPath (mapDist (coordinateRestriction S) u.1)
  exact LinearMap.congr_fun (rawCanonicalPath_coordinateRestriction S) u.1

/-- A distribution invisible on `S` has a canonical path invisible on `S`. -/
theorem canonicalPath_mem_coordinateRestriction_ker (S : Set ι)
    {u : RedDist (Configuration ι G)}
    (hu : u ∈ LinearMap.ker (mapRedDist (coordinateRestriction S))) :
    canonicalPath u ∈
      LinearMap.ker
        (mapPath (coordinateRestriction S) (coordinateRestriction S)) := by
  rw [LinearMap.mem_ker] at hu ⊢
  have h := LinearMap.congr_fun (canonicalPath_coordinateRestriction S) u
  change
    mapPath (coordinateRestriction S) (coordinateRestriction S)
        (canonicalPath u) =
      canonicalPath (mapRedDist (coordinateRestriction S) u) at h
  rw [h, hu, map_zero]

end GeneralSphereT.PathAlgebra
