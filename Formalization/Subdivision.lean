import Formalization.ReducedBoundary

set_option linter.style.header false

/-!
# Ordered coordinate paths

This file formalizes the telescoping core of equations (2.13)--(2.16).  A
configuration is a finitely supported coordinate function.  Its coordinates
are traversed in the fixed linear order, producing only one-coordinate edges.
-/

noncomputable section

open scoped BigOperators

namespace GeneralSphereT.PathAlgebra

section Telescoping

variable {ι A B : Type*} [LinearOrder ι] [AddCommGroup A] [AddCommGroup B]

/-- Sum of the steps indexed strictly before `i` in a finite ordered set. -/
def prefixSum (s : Finset ι) (step : ι → A) (i : ι) : A :=
  ∑ j ∈ s.filter fun j => j < i, step j

/-- A finite sequence of coordinate steps telescopes in increasing order. -/
theorem sum_step_telescopes (s : Finset ι) (step : ι → A) (F : A → B) (x : A) :
    (∑ i ∈ s,
        (F (x + prefixSum s step i + step i) -
          F (x + prefixSum s step i))) =
      F (x + ∑ i ∈ s, step i) - F x := by
  induction s using Finset.induction_on_max with
  | empty => simp [prefixSum]
  | @insert a s hmax ih =>
      have ha : a ∉ s := by
        intro ha
        exact (lt_irrefl a) (hmax a ha)
      have hprefix_a : prefixSum (insert a s) step a = ∑ i ∈ s, step i := by
        have hfilter : (insert a s).filter (fun j => j < a) = s := by
          ext j
          simp only [Finset.mem_filter, Finset.mem_insert]
          constructor
          · rintro ⟨hj, hja⟩
            rcases hj with rfl | hj
            · exact (lt_irrefl _ hja).elim
            · exact hj
          · intro hj
            exact ⟨Or.inr hj, hmax j hj⟩
        unfold prefixSum
        rw [hfilter]
      have hprefix_old (i : ι) (hi : i ∈ s) :
          prefixSum (insert a s) step i = prefixSum s step i := by
        have hai : ¬a < i := not_lt_of_ge (hmax i hi).le
        have hfilter : (insert a s).filter (fun j => j < i) =
            s.filter (fun j => j < i) := by
          ext j
          simp only [Finset.mem_filter, Finset.mem_insert]
          constructor
          · rintro ⟨hj, hji⟩
            rcases hj with rfl | hj
            · exact (hai hji).elim
            · exact ⟨hj, hji⟩
          · rintro ⟨hj, hji⟩
            exact ⟨Or.inr hj, hji⟩
        unfold prefixSum
        rw [hfilter]
      rw [Finset.sum_insert ha]
      rw [hprefix_a]
      have hold :
          (∑ i ∈ s,
              (F (x + prefixSum (insert a s) step i + step i) -
                F (x + prefixSum (insert a s) step i))) =
            ∑ i ∈ s,
              (F (x + prefixSum s step i + step i) -
                F (x + prefixSum s step i)) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [hprefix_old i hi]
      rw [hold, ih, Finset.sum_insert ha]
      abel_nf

end Telescoping

section OrderedPath

variable {ι G : Type*} [LinearOrder ι] [AddCommGroup G]

/-- A finitely supported coordinate configuration. -/
abbrev Configuration (ι G : Type*) [Zero G] := ι →₀ G

/-- The part of `r` supported in coordinates strictly below `i`. -/
def coordinatePrefix (r : Configuration ι G) (i : ι) : Configuration ι G :=
  prefixSum r.support (fun j => Finsupp.single j (r j)) i

/-- Replace the coordinates one at a time, in increasing order. -/
def orderedPath (r x : Configuration ι G) :
    Path (Configuration ι G) (Configuration ι G) :=
  ∑ i ∈ r.support,
    edge (Finsupp.single i (r i)) (x + coordinatePrefix r i)

omit [LinearOrder ι] in
theorem sum_single_support (r : Configuration ι G) :
    (∑ i ∈ r.support, Finsupp.single i (r i)) = r := by
  change r.sum (fun i g => Finsupp.single i g) = r
  exact Finsupp.sum_single r

@[simp]
theorem orderedPath_zero (x : Configuration ι G) : orderedPath 0 x = 0 := by
  simp [orderedPath]

/-- The ordered path has the expected primitive endpoint boundary. -/
theorem primitiveBoundary_orderedPath (r x : Configuration ι G) :
    primitiveBoundary (Configuration ι G) (orderedPath r x) =
      bracket (x + r) - bracket x := by
  rw [orderedPath, map_sum]
  simp only [boundary_edge, AddMonoidHom.id_apply]
  rw [show (∑ i ∈ r.support,
      (bracket (x + coordinatePrefix r i + Finsupp.single i (r i)) -
        bracket (x + coordinatePrefix r i))) =
      bracket (x + ∑ i ∈ r.support, Finsupp.single i (r i)) - bracket x by
    simpa only [coordinatePrefix] using
      (sum_step_telescopes r.support
        (fun i => Finsupp.single i (r i)) bracket x)]
  rw [sum_single_support]

/-- Traverse the coordinates in order while the base moves along `φ`. -/
def orderedPathAlong {X : Type*} [AddCommGroup X]
    (φ : Configuration ι G →+ X) (r : Configuration ι G) (x : X) :
    Path (Configuration ι G) X :=
  ∑ i ∈ r.support,
    edge (Finsupp.single i (r i)) (x + φ (coordinatePrefix r i))

/-- An ordered path along `φ` has the expected endpoints. -/
theorem boundary_orderedPathAlong {X : Type*} [AddCommGroup X]
    (φ : Configuration ι G →+ X) (r : Configuration ι G) (x : X) :
    boundary φ (orderedPathAlong φ r x) =
      bracket (x + φ r) - bracket x := by
  rw [orderedPathAlong, map_sum]
  simp only [boundary_edge]
  rw [show
      (∑ i ∈ r.support,
          (bracket
              (x + φ (coordinatePrefix r i) +
                φ (Finsupp.single i (r i))) -
            bracket (x + φ (coordinatePrefix r i)))) =
        bracket
            (x + ∑ i ∈ r.support, φ (Finsupp.single i (r i))) -
          bracket x by
      simpa only [coordinatePrefix, prefixSum, map_sum] using
        (sum_step_telescopes r.support
          (fun i => φ (Finsupp.single i (r i))) bracket x)]
  rw [← map_sum, sum_single_support]

/-- For the identity map, `orderedPathAlong` is the primitive ordered path. -/
theorem orderedPathAlong_id (r x : Configuration ι G) :
    orderedPathAlong (AddMonoidHom.id (Configuration ι G)) r x =
      orderedPath r x := by
  simp [orderedPathAlong, orderedPath]

/-- Applying `d_*` transports precisely the base points of an ordered path. -/
theorem mapDPath_orderedPath {B : Type*} [AddCommGroup B]
    (d : Configuration ι G →+ B) (r c : Configuration ι G) :
    mapDPath d (orderedPath r c) = orderedPathAlong d r (d c) := by
  simp [orderedPath, orderedPathAlong]

/-- Linear extension of ordered subdivision before the path quotient. -/
def rawSubdivision :
    RawPath (Configuration ι G) (Configuration ι G) →ₗ[ℤ]
      Path (Configuration ι G) (Configuration ι G) :=
  Finsupp.linearCombination ℤ fun p => orderedPath p.1 p.2

@[simp]
theorem rawSubdivision_rawEdge (r x : Configuration ι G) :
    rawSubdivision (rawEdge r x) = orderedPath r x := by
  simp [rawSubdivision, rawEdge]

/-- Ordered subdivision kills the zero-increment quotient relations. -/
theorem zeroIncrement_le_rawSubdivision_ker :
    zeroIncrement (Configuration ι G) (Configuration ι G) ≤
      LinearMap.ker rawSubdivision := by
  change Submodule.span ℤ
      (Set.range fun x : Configuration ι G =>
        Finsupp.single ((0 : Configuration ι G), x) 1) ≤
    LinearMap.ker rawSubdivision
  rw [Submodule.span_le]
  rintro _ ⟨x, rfl⟩
  change rawSubdivision (rawEdge 0 x) = 0
  simp

/-- The ordered subdivision map on primitive path classes. -/
def subdivision :
    Path (Configuration ι G) (Configuration ι G) →ₗ[ℤ]
      Path (Configuration ι G) (Configuration ι G) :=
  (zeroIncrement (Configuration ι G) (Configuration ι G)).liftQ
    rawSubdivision zeroIncrement_le_rawSubdivision_ker

@[simp]
theorem subdivision_edge (r x : Configuration ι G) :
    subdivision (edge r x) = orderedPath r x := by
  simp [subdivision, edge]

/-- Before quotienting, subdivision preserves the primitive boundary. -/
theorem primitiveBoundary_rawSubdivision :
    (primitiveBoundary (Configuration ι G)).comp rawSubdivision =
      rawBoundary (AddMonoidHom.id (Configuration ι G)) := by
  ext p
  simp [rawSubdivision, rawBoundary, primitiveBoundary_orderedPath]

/-- This is the primitive part of equation (2.14): `∂ sd = ∂`. -/
theorem primitiveBoundary_subdivision :
    (primitiveBoundary (Configuration ι G)).comp subdivision =
      primitiveBoundary (Configuration ι G) := by
  apply LinearMap.ext
  intro p
  refine Submodule.Quotient.induction_on
    (p := zeroIncrement (Configuration ι G) (Configuration ι G)) p ?_
  intro q
  change primitiveBoundary (Configuration ι G) (rawSubdivision q) =
    rawBoundary (AddMonoidHom.id (Configuration ι G)) q
  exact LinearMap.congr_fun primitiveBoundary_rawSubdivision q

/-- Send a configuration generator to the ordered path from zero to it. -/
def rawCanonicalPath :
    Dist (Configuration ι G) →ₗ[ℤ]
      Path (Configuration ι G) (Configuration ι G) :=
  Finsupp.linearCombination ℤ fun c => orderedPath c 0

@[simp]
theorem rawCanonicalPath_single (c : Configuration ι G) (n : ℤ) :
    rawCanonicalPath (Finsupp.single c n) = n • orderedPath c 0 := by
  simp [rawCanonicalPath]

/-- The canonical path map on reduced distributions. -/
def canonicalPath :
    RedDist (Configuration ι G) →ₗ[ℤ]
      Path (Configuration ι G) (Configuration ι G) :=
  rawCanonicalPath.comp (RedDist (Configuration ι G)).subtype

@[simp]
theorem canonicalPath_redBracket (c : Configuration ι G) :
    canonicalPath (redBracket c) = orderedPath c 0 := by
  simp [canonicalPath, redBracket, bracket]

/-- Linear combination of the reduced generators `bracket c`. -/
def bracketCombination :
    Dist (Configuration ι G) →ₗ[ℤ] Dist (Configuration ι G) :=
  Finsupp.linearCombination ℤ bracket

omit [LinearOrder ι] in
@[simp]
theorem bracketCombination_single (c : Configuration ι G) (n : ℤ) :
    bracketCombination (Finsupp.single c n) = n • bracket c := by
  simp [bracketCombination]

omit [LinearOrder ι] in
/-- Combining reduced generators subtracts the augmentation at the zero basis vector. -/
theorem bracketCombination_apply (u : Dist (Configuration ι G)) :
    bracketCombination u =
      u - augmentation (Configuration ι G) u •
        Finsupp.single (0 : Configuration ι G) 1 := by
  classical
  induction u using Finsupp.induction with
  | zero => simp [bracketCombination]
  | single_add c n u _ _ ih =>
      simp only [map_add, bracketCombination_single, augmentation_single, ih]
      simp [bracket, smul_sub, add_smul]
      abel_nf

/-- On all distributions, the canonical path has boundary `bracketCombination`. -/
theorem primitiveBoundary_rawCanonicalPath :
    (primitiveBoundary (Configuration ι G)).comp rawCanonicalPath =
      bracketCombination := by
  ext c
  simp [rawCanonicalPath, bracketCombination, primitiveBoundary_orderedPath]

/-- Equation (2.16): the canonical path is a right inverse to reduced boundary. -/
theorem primitiveReducedBoundary_canonicalPath :
    (primitiveReducedBoundary (Configuration ι G)).comp canonicalPath =
      LinearMap.id := by
  apply LinearMap.ext
  intro u
  apply Subtype.ext
  change primitiveBoundary (Configuration ι G) (rawCanonicalPath u.1) = u.1
  have hboundary := LinearMap.congr_fun primitiveBoundary_rawCanonicalPath u.1
  change primitiveBoundary (Configuration ι G) (rawCanonicalPath u.1) =
    bracketCombination u.1 at hboundary
  rw [hboundary]
  rw [bracketCombination_apply]
  simp

end OrderedPath

end GeneralSphereT.PathAlgebra
