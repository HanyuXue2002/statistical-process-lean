import Formalization.Cells
import Formalization.CoordinateRestriction
import Formalization.DistributionDifferences
import Formalization.ElementaryPaths
import Formalization.LocalIdentity

set_option linter.style.header false

/-!
# Coefficients of a fixed oriented edge type

Because `Path I X` is quotiented only by the zero-increment generators, every
nonzero increment `r` has a well-defined coefficient distribution: collect the
coefficients of all edges `[r; x]`, retaining `x` as the basis element of a
distribution on `X`.  This is the algebraic operation needed when the proof of
(2.26) groups a path by its complete oriented cell type.

This module deliberately stops at this coefficient-extraction layer.  In
particular, they do not assert the full reverse inclusion in (2.26).
-/

noncomputable section

namespace GeneralSphereT.PathAlgebra

section CoefficientExtractor

variable {I X : Type*} [AddCommGroup I]

local instance instDecidableEqI : DecidableEq I := Classical.decEq I

/-- Before taking the path quotient, collect the bases of all `r`-edges. -/
def rawPathCoefficient (r : I) : RawPath I X →ₗ[ℤ] Dist X :=
  Finsupp.linearCombination ℤ fun p =>
    if p.1 = r then Finsupp.single p.2 1 else 0

omit [AddCommGroup I] in
@[simp]
theorem rawPathCoefficient_rawEdge (r s : I) (x : X) :
    rawPathCoefficient r (rawEdge s x) =
      if s = r then Finsupp.single x 1 else 0 := by
  classical
  simp [rawPathCoefficient, rawEdge]

/-- A fixed nonzero label does not see any zero-increment relation. -/
theorem zeroIncrement_le_rawPathCoefficient_ker
    (r : I) (hr : r ≠ 0) :
    zeroIncrement I X ≤ LinearMap.ker (rawPathCoefficient r) := by
  rw [zeroIncrement, Submodule.span_le]
  rintro _ ⟨x, rfl⟩
  change rawPathCoefficient r (rawEdge 0 x) = 0
  have h0r : (0 : I) ≠ r := Ne.symm hr
  simp [h0r]

/--
The coefficient distribution of the complete oriented edge type `r`.

The hypothesis `r ≠ 0` is essential: zero-labelled generators are precisely
the relations killed in `Path I X`.
-/
def pathCoefficient (r : I) (hr : r ≠ 0) :
    Path I X →ₗ[ℤ] Dist X :=
  (zeroIncrement I X).liftQ
    (rawPathCoefficient r) (zeroIncrement_le_rawPathCoefficient_ker r hr)

@[simp]
theorem pathCoefficient_edge (r : I) (hr : r ≠ 0) (s : I) (x : X) :
    pathCoefficient r hr (edge s x) =
      if s = r then Finsupp.single x 1 else 0 := by
  classical
  simp [pathCoefficient, edge]

@[simp]
theorem pathCoefficient_edge_self (r : I) (hr : r ≠ 0) (x : X) :
    pathCoefficient r hr (edge r x) = Finsupp.single x 1 := by
  simp

@[simp]
theorem pathCoefficient_edge_of_ne (r : I) (hr : r ≠ 0)
    {s : I} (hsr : s ≠ r) (x : X) :
    pathCoefficient r hr (edge s x) = 0 := by
  simp [hsr]

end CoefficientExtractor

section Translation

variable {I X : Type*} [AddCommGroup I] [AddCommGroup X]

/-- Collecting a fixed edge type commutes with translation of its base. -/
theorem pathCoefficient_baseTranslation_map
    (r : I) (hr : r ≠ 0) (u : X) :
    (pathCoefficient r hr).comp (baseTranslation u) =
      (distributionTranslation u).comp (pathCoefficient r hr) := by
  ext p x
  change
    (pathCoefficient r hr (baseTranslation u (edge p.1 p.2))) x =
      (distributionTranslation u (pathCoefficient r hr (edge p.1 p.2))) x
  by_cases hpr : p.1 = r
  · simp [hpr]
  · simp [hpr]

@[simp]
theorem pathCoefficient_baseTranslation
    (r : I) (hr : r ≠ 0) (u : X) (p : Path I X) :
    pathCoefficient r hr (baseTranslation u p) =
      distributionTranslation u (pathCoefficient r hr p) := by
  exact LinearMap.congr_fun (pathCoefficient_baseTranslation_map r hr u) p

/-- Collecting a fixed edge type commutes with the difference `T_u - 1`. -/
@[simp]
theorem pathCoefficient_baseDifference
    (r : I) (hr : r ≠ 0) (u : X) (p : Path I X) :
    pathCoefficient r hr (baseDifference u p) =
      distributionDifference u (pathCoefficient r hr p) := by
  simp [baseDifference, distributionDifference]

end Translation

section Pushforward

variable {I J X Y : Type*}
variable [AddCommGroup I] [AddCommGroup J]
variable [AddCommGroup X] [AddCommGroup Y]

/-- An injective increment map preserves the coefficient of every fixed type. -/
theorem pathCoefficient_mapPath_of_injective
    (i : I →+ J) (b : X →+ Y) (hi : Function.Injective i)
    (r : I) (hr : r ≠ 0) (p : Path I X) :
    pathCoefficient (i r) (fun hir => hr (hi (by simpa using hir)))
        (mapPath i b p) =
      mapDist b (pathCoefficient r hr p) := by
  let hir : i r ≠ 0 := fun h => hr (hi (by simpa using h))
  have hmaps :
      (pathCoefficient (i r) hir).comp (mapPath i b) =
        (mapDist b).comp (pathCoefficient r hr) := by
    ext q y
    change
      (pathCoefficient (i r) hir (mapPath i b (edge q.1 q.2))) y =
        (mapDist b (pathCoefficient r hr (edge q.1 q.2))) y
    by_cases hqr : q.1 = r
    · simp [hqr]
    · have hiqr : i q.1 ≠ i r := fun h => hqr (hi h)
      simp [hqr, hiqr]
  exact LinearMap.congr_fun hmaps p

/-- In particular, changing only the base labels preserves every coefficient. -/
theorem pathCoefficient_mapPath_id
    (b : X →+ Y) (r : I) (hr : r ≠ 0) (p : Path I X) :
    pathCoefficient r hr (mapPath (AddMonoidHom.id I) b p) =
      mapDist b (pathCoefficient r hr p) := by
  simpa using
    (pathCoefficient_mapPath_of_injective
      (AddMonoidHom.id I) b Function.injective_id r hr p)

/-- The coefficient form of the paper's base-label pushforward `d_*`. -/
theorem pathCoefficient_mapDPath
    (d : X →+ Y) (r : X) (hr : r ≠ 0) (p : Path X X) :
    pathCoefficient r hr (mapDPath d p) =
      mapDist d (pathCoefficient r hr p) := by
  exact pathCoefficient_mapPath_id d r hr p

end Pushforward

section CellFormulas

variable {I X : Type*} [AddCommGroup I] [AddCommGroup X]

local instance instDecidableEqICell : DecidableEq I := Classical.decEq I

/-- Coefficients of a square, with all possible label coincidences retained. -/
theorem pathCoefficient_square
    (r : I) (hr : r ≠ 0) (φ : I →+ X) (s t : I) (x : X) :
    pathCoefficient r hr (square φ s t x) =
      (if s = r then
        Finsupp.single x 1 - Finsupp.single (x + φ t) 1
      else 0) +
      (if t = r then
        Finsupp.single (x + φ s) 1 - Finsupp.single x 1
      else 0) := by
  classical
  simp only [square, map_sub, map_add, pathCoefficient_edge]
  by_cases hs : s = r <;> by_cases ht : t = r <;>
    simp [hs, ht]

/-- For distinct labels, the `s`-coefficient is one negative difference. -/
theorem pathCoefficient_square_left
    (s : I) (hs : s ≠ 0) {t : I} (hst : t ≠ s)
    (φ : I →+ X) (x : X) :
    pathCoefficient s hs (square φ s t x) =
      -distributionDifference (φ t) (Finsupp.single x 1) := by
  rw [pathCoefficient_square]
  simp [hst, distributionDifference]

/-- For distinct labels, the `t`-coefficient is one positive difference. -/
theorem pathCoefficient_square_right
    {s : I} (t : I) (ht : t ≠ 0) (hst : s ≠ t)
    (φ : I →+ X) (x : X) :
    pathCoefficient t ht (square φ s t x) =
      distributionDifference (φ s) (Finsupp.single x 1) := by
  rw [pathCoefficient_square]
  simp [hst, distributionDifference]

/-- Coefficients of a triangle, again allowing arbitrary label coincidences. -/
theorem pathCoefficient_triangle
    (r : I) (hr : r ≠ 0) (φ : I →+ X) (g h : I) (x : X) :
    pathCoefficient r hr (triangle φ g h x) =
      (if g = r then Finsupp.single x 1 else 0) +
      (if h = r then Finsupp.single (x + φ g) 1 else 0) -
      (if g + h = r then Finsupp.single x 1 else 0) := by
  classical
  simp [triangle]

end CellFormulas

section ElementaryFiber

variable {ι G J X Y : Type*}
variable [LinearOrder ι] [AddCommGroup G] [AddCommGroup J]
variable [AddCommGroup X] [AddCommGroup Y]

/-!
Global injectivity is stronger than coordinate restriction provides.  On the
elementary subgroup one only needs the fiber of the chosen surviving label to
contain no other elementary label.  The next statement isolates that exact
hypothesis.
-/

theorem pathCoefficient_mapPath_elementary_of_fiber
    (i : Configuration ι G →+ J) (b : X →+ Y)
    (r : Configuration ι G) (hr : r ≠ 0) (hir : i r ≠ 0)
    (hfiber : ∀ (j : ι) (g : G), g ≠ 0 →
      (i (Finsupp.single j g) = i r ↔ Finsupp.single j g = r))
    {p : Path (Configuration ι G) X}
    (hp : p ∈ elementaryPaths (ι := ι) (G := G) (X := X)) :
    pathCoefficient (i r) hir (mapPath i b p) =
      mapDist b (pathCoefficient r hr p) := by
  classical
  change p ∈ Submodule.span ℤ
    {q | ∃ (j : ι) (g : G) (x : X),
      g ≠ 0 ∧ q = edge (Finsupp.single j g) x} at hp
  induction hp using Submodule.span_induction with
  | mem p hp =>
      rcases hp with ⟨j, g, x, hg, rfl⟩
      have hiff := hfiber j g hg
      by_cases hlabel : Finsupp.single j g = r
      · simp [hlabel]
      · have himage : i (Finsupp.single j g) ≠ i r :=
          fun h => hlabel (hiff.mp h)
        simp [hlabel, himage]
  | zero => simp
  | add p q hp hq ihp ihq => simp [ihp, ihq]
  | smul n p hp ih => simp [ih]

/--
Among nonzero elementary labels, restriction has a singleton fiber over a
label whose coordinate survives.
-/
theorem coordinateRestriction_single_fiber
    (S : Set ι) (i : ι) (hi : i ∈ S) (g : G) (hg : g ≠ 0)
    (j : ι) (h : G) (hh : h ≠ 0) :
    coordinateRestriction S (Finsupp.single j h) =
        coordinateRestriction S (Finsupp.single i g) ↔
      Finsupp.single j h = Finsupp.single i g := by
  constructor
  · intro heq
    by_cases hj : j ∈ S
    · rw [coordinateRestriction_single_mem S hj,
          coordinateRestriction_single_mem S hi] at heq
      by_cases hji : j = i
      · subst j
        have hhg : h = g := by
          simpa using congrArg (fun c => c ⟨i, hi⟩) heq
        subst h
        rfl
      · have hij : i ≠ j := Ne.symm hji
        have hz : h = 0 := by
          simpa [Finsupp.single_apply, hij] using
            congrArg (fun c => c ⟨j, hj⟩) heq
        exact (hh hz).elim
    · rw [coordinateRestriction_single_not_mem S hj,
          coordinateRestriction_single_mem S hi] at heq
      have hzg : (0 : G) = g := by
        simpa using congrArg (fun c => c ⟨i, hi⟩) heq
      exact (hg hzg.symm).elim
  · intro hsingle
    exact congrArg (coordinateRestriction S) hsingle

/--
Coefficient compatibility for a surviving elementary label under coordinate
restriction.  No false global-injectivity claim is needed: the path itself is
assumed elementary, and the preceding singleton-fiber lemma is exactly what
the span induction uses.
-/
theorem pathCoefficient_coordinateRestriction_elementary
    (S : Set ι) (i : ι) (hi : i ∈ S) (g : G) (hg : g ≠ 0)
    (b : X →+ Y) {p : Path (Configuration ι G) X}
    (hp : p ∈ elementaryPaths (ι := ι) (G := G) (X := X)) :
    pathCoefficient
        (coordinateRestriction S (Finsupp.single i g))
        (by
          rw [coordinateRestriction_single_mem S hi]
          intro hz
          have hzg : g = 0 := by
            simpa using congrArg (fun c => c ⟨i, hi⟩) hz
          exact hg hzg)
        (mapPath (coordinateRestriction S) b p) =
      mapDist b (pathCoefficient (Finsupp.single i g)
        (by
          intro hz
          have hzg : g = 0 := by
            simpa using congrArg (fun c => c i) hz
          exact hg hzg) p) := by
  let r : Configuration ι G := Finsupp.single i g
  have hr : r ≠ 0 := by
    intro hz
    have hzg : g = 0 := by
      simpa [r] using congrArg (fun c => c i) hz
    exact hg hzg
  have hir : coordinateRestriction S r ≠ 0 := by
    rw [show coordinateRestriction S r =
        Finsupp.single ⟨i, hi⟩ g by
      simp [r, hi]]
    intro hz
    have hzg : g = 0 := by
      simpa using congrArg (fun c => c ⟨i, hi⟩) hz
    exact hg hzg
  exact pathCoefficient_mapPath_elementary_of_fiber
    (coordinateRestriction S) b r hr hir
      (fun j h hh => by
        simpa [r] using
          coordinateRestriction_single_fiber S i hi g hg j h hh)
      hp

end ElementaryFiber

end GeneralSphereT.PathAlgebra
