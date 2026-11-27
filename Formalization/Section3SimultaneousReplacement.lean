import Formalization.ElementaryPathCoefficientDecomposition
import Formalization.Section3LocalCubeReplacement

set_option linter.style.header false

/-!
# Section 3: simultaneous replacement of complete operator labels

The coefficient decomposition of an elementary path is finite.  If every
complete label can be replaced by a word in a prescribed class of labels and
the linearized one-edge-minus-word error of its coefficient distribution lies
in the identity denominator, then all labels can be replaced simultaneously.
The resulting path uses only the prescribed labels and differs from the
original path by an element of the denominator.
-/

noncomputable section

namespace GeneralSphereT.PathAlgebra

universe uF uB

section WordDistributions

variable {I X : Type*} [AddCommGroup I] [AddCommGroup X]

/-- Linear extension of a fixed word path over all integral base
distributions. -/
def wordDistribution (φ : I →+ X) (word : List I) :
    Dist X →ₗ[ℤ] Path I X :=
  Finsupp.linearCombination ℤ (wordPath φ word)

@[simp]
theorem wordDistribution_single (φ : I →+ X) (word : List I)
    (x : X) (n : ℤ) :
    wordDistribution φ word (Finsupp.single x n) =
      n • wordPath φ word x := by
  simp [wordDistribution]

/-- Label-by-label, the original edge distribution minus its replacement
word distribution is exactly the linearized square-strip error. -/
theorem edgeDistribution_sub_wordDistribution
    (φ : I →+ X) (t : I) (word : List I) (z : Dist X) :
    edgeDistribution t z - wordDistribution φ word z =
      ellDistribution φ t word z := by
  let hmaps :
      edgeDistribution t - wordDistribution φ word =
        ellDistribution φ t word := by
    ext x
    simp [ell, edgeDistribution, wordDistribution, ellDistribution]
  exact LinearMap.congr_fun hmaps z

end WordDistributions

section RestrictedLabels

variable {ι G B : Type*}
variable [LinearOrder ι] [AddCommGroup G] [AddCommGroup B]

/-- Elementary paths whose complete nonzero labels satisfy the predicate. -/
def restrictedElementaryPaths (P : Configuration ι G → Prop) :
    Submodule ℤ (Path (Configuration ι G) B) :=
  Submodule.span ℤ
    {p | ∃ (r : Configuration ι G) (a : B),
      IsElementaryLabel r ∧ P r ∧ p = edge r a}

omit [LinearOrder ι] [AddCommGroup B] in
theorem edge_mem_restrictedElementaryPaths
    (P : Configuration ι G → Prop)
    {r : Configuration ι G} (hr : IsElementaryLabel r) (hP : P r)
    (a : B) :
    edge r a ∈ restrictedElementaryPaths (B := B) P :=
  Submodule.subset_span ⟨r, a, hr, hP, rfl⟩

omit [LinearOrder ι] in
/-- A word all of whose labels are allowed is an allowed elementary path. -/
theorem wordPath_mem_restrictedElementaryPaths
    (P : Configuration ι G → Prop)
    (d : Configuration ι G →+ B)
    (word : List (Configuration ι G))
    (hword : ∀ u ∈ word, IsElementaryLabel u ∧ P u)
    (a : B) :
    wordPath d word a ∈ restrictedElementaryPaths (B := B) P := by
  induction word generalizing a with
  | nil => simp [wordPath]
  | cons u word ih =>
      simp only [wordPath]
      apply Submodule.add_mem
      · exact edge_mem_restrictedElementaryPaths P
          (hword u (by simp)).1 (hword u (by simp)).2 a
      · apply ih
        intro w hw
        exact hword w (by simp [hw])

omit [LinearOrder ι] in
/-- Linearizing an allowed word over any distribution stays in the allowed
elementary submodule. -/
theorem wordDistribution_mem_restrictedElementaryPaths
    (P : Configuration ι G → Prop)
    (d : Configuration ι G →+ B)
    (word : List (Configuration ι G))
    (hword : ∀ u ∈ word, IsElementaryLabel u ∧ P u)
    (z : Dist B) :
    wordDistribution d word z ∈ restrictedElementaryPaths (B := B) P := by
  induction z using Finsupp.induction with
  | zero => simp
  | single_add a n z _ _ ih =>
      rw [map_add, wordDistribution_single]
      exact Submodule.add_mem _
        (Submodule.smul_mem _ n
          (wordPath_mem_restrictedElementaryPaths P d word hword a))
        ih

universe uFacet uBA

variable {Facet : Type uFacet}
variable {BAt : Facet → Type uBA} [∀ ρ, AddCommGroup (BAt ρ)]
variable {facets : Facet → Set ι}
variable {d : Configuration ι G →+ B}
variable (L : FacetRestrictionData
  (CAt := fun ρ => Configuration (facets ρ) G)
  (BAt := BAt) (Facet := Facet) d)

/-- Finite simultaneous replacement modulo the physical identity
denominator.  The hypothesis is deliberately labelwise: local tau and the
square-strip theorem discharge it for apex labels, while an already allowed
label uses the singleton word and has zero error. -/
theorem simultaneousReplacement_exists
    (P : Configuration ι G → Prop)
    (p : Path (Configuration ι G) B)
    (hp : p ∈ elementaryPaths (ι := ι) (G := G) (X := B))
    (hreplace : ∀ (r : Configuration ι G) (hr : r ≠ 0),
      IsElementaryLabel r →
      ∃ word : List (Configuration ι G),
        (∀ u ∈ word, IsElementaryLabel u ∧ P u) ∧
        ellDistribution d r word (pathCoefficient r hr p) ∈
          physicalIdentityPaths L) :
    ∃ pbot : Path (Configuration ι G) B,
      pbot ∈ restrictedElementaryPaths (B := B) P ∧
      p - pbot ∈ physicalIdentityPaths L := by
  classical
  obtain ⟨S, hS, _, hrec⟩ :=
    elementaryPath_exists_pathCoefficient_decomposition p hp
  choose words hwords herrors using
    fun r : S => hreplace r.1 (hS r.1 r.2).1 (hS r.1 r.2).2
  let pbot : Path (Configuration ι G) B :=
    ∑ r : S, wordDistribution d (words r)
      (pathCoefficient r.1 (hS r.1 r.2).1 p)
  refine ⟨pbot, ?_, ?_⟩
  · apply Submodule.sum_mem
    intro r _
    exact wordDistribution_mem_restrictedElementaryPaths
      P d (words r) (hwords r)
        (pathCoefficient r.1 (hS r.1 r.2).1 p)
  · have hdiff :
        p - pbot =
          ∑ r : S, ellDistribution d r.1 (words r)
            (pathCoefficient r.1 (hS r.1 r.2).1 p) := by
      calc
        p - pbot =
            (∑ r : S, edgeDistribution r.1
              (pathCoefficient r.1 (hS r.1 r.2).1 p)) - pbot :=
          congrArg (fun q => q - pbot) hrec
        _ = ∑ r : S, ellDistribution d r.1 (words r)
              (pathCoefficient r.1 (hS r.1 r.2).1 p) := by
          simp only [pbot, ← Finset.sum_sub_distrib]
          apply Fintype.sum_congr
          intro r
          exact edgeDistribution_sub_wordDistribution d r.1 (words r)
            (pathCoefficient r.1 (hS r.1 r.2).1 p)
    rw [hdiff]
    exact Submodule.sum_mem _ fun r _ => herrors r

end RestrictedLabels

end GeneralSphereT.PathAlgebra
