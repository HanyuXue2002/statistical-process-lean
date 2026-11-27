import Formalization.ElementaryPaths

set_option linter.style.header false

/-!
# Elementary image of physical subdivision

Physical ordered subdivision has elementary image.  Consequently the two
naturality identities in (2.14) can be stated with the precise elementary
subgroups as codomains.
-/

noncomputable section

namespace GeneralSphereT.PathAlgebra

variable {ι G X : Type*}
variable [LinearOrder ι] [AddCommGroup G] [AddCommGroup X]

/-- The raw physical subdivision is a linear combination of elementary paths. -/
theorem rawSubdivisionAlong_mem (φ : Configuration ι G →+ X)
    (p : RawPath (Configuration ι G) X) :
    rawSubdivisionAlong φ p ∈
      elementaryPaths (ι := ι) (G := G) (X := X) := by
  classical
  induction p using Finsupp.induction with
  | zero => simp
  | single_add a n p _ _ ih =>
      rw [map_add]
      apply Submodule.add_mem
      · simpa [rawSubdivisionAlong] using
          (Submodule.smul_mem
            (elementaryPaths (ι := ι) (G := G) (X := X)) n
            (orderedPathAlong_mem φ a.1 a.2))
      · exact ih

/-- Physical subdivision on path classes has elementary image. -/
theorem subdivisionAlong_mem (φ : Configuration ι G →+ X)
    (p : Path (Configuration ι G) X) :
    subdivisionAlong φ p ∈
      elementaryPaths (ι := ι) (G := G) (X := X) := by
  refine Submodule.Quotient.induction_on
    (p := zeroIncrement (Configuration ι G) X) p ?_
  intro q
  change rawSubdivisionAlong φ q ∈
    elementaryPaths (ι := ι) (G := G) (X := X)
  exact rawSubdivisionAlong_mem φ q

/-- Raw physical subdivision with its elementary image recorded in the type. -/
def rawSubdivisionAlongElementary (φ : Configuration ι G →+ X) :
    RawPath (Configuration ι G) X →ₗ[ℤ]
      elementaryPaths (ι := ι) (G := G) (X := X) :=
  LinearMap.codRestrict
    (elementaryPaths (ι := ι) (G := G) (X := X))
    (rawSubdivisionAlong φ) (rawSubdivisionAlong_mem φ)

/-- Physical subdivision with its elementary image recorded in the type. -/
def subdivisionAlongElementary (φ : Configuration ι G →+ X) :
    Path (Configuration ι G) X →ₗ[ℤ]
      elementaryPaths (ι := ι) (G := G) (X := X) :=
  LinearMap.codRestrict
    (elementaryPaths (ι := ι) (G := G) (X := X))
    (subdivisionAlong φ) (subdivisionAlong_mem φ)

@[simp]
theorem rawSubdivisionAlongElementary_coe (φ : Configuration ι G →+ X)
    (p : RawPath (Configuration ι G) X) :
    ((rawSubdivisionAlongElementary φ p :
        elementaryPaths (ι := ι) (G := G) (X := X)) :
      Path (Configuration ι G) X) = rawSubdivisionAlong φ p :=
  rfl

@[simp]
theorem subdivisionAlongElementary_coe (φ : Configuration ι G →+ X)
    (p : Path (Configuration ι G) X) :
    ((subdivisionAlongElementary φ p :
        elementaryPaths (ι := ι) (G := G) (X := X)) :
      Path (Configuration ι G) X) = subdivisionAlong φ p :=
  rfl

/-- Boundary restricted to the elementary subgroup. -/
def elementaryBoundary (φ : Configuration ι G →+ X) :
    elementaryPaths (ι := ι) (G := G) (X := X) →ₗ[ℤ] Dist X :=
  (boundary φ).comp
    (elementaryPaths (ι := ι) (G := G) (X := X)).subtype

/-- Reduced boundary restricted to the elementary subgroup. -/
def elementaryReducedBoundary (φ : Configuration ι G →+ X) :
    elementaryPaths (ι := ι) (G := G) (X := X) →ₗ[ℤ] RedDist X :=
  (reducedBoundary φ).comp
    (elementaryPaths (ι := ι) (G := G) (X := X)).subtype

/-- Physical subdivision preserves boundary after sharpening its codomain. -/
theorem elementaryBoundary_subdivisionAlongElementary
    (φ : Configuration ι G →+ X) :
    (elementaryBoundary φ).comp (subdivisionAlongElementary φ) =
      boundary φ := by
  apply LinearMap.ext
  intro p
  change boundary φ (subdivisionAlong φ p) = boundary φ p
  exact LinearMap.congr_fun (boundary_subdivisionAlong φ) p

/-- The fully reduced-typed physical boundary identity from (2.14). -/
theorem elementaryReducedBoundary_subdivisionAlongElementary
    (φ : Configuration ι G →+ X) :
    (elementaryReducedBoundary φ).comp (subdivisionAlongElementary φ) =
      reducedBoundary φ := by
  apply LinearMap.ext
  intro p
  apply Subtype.ext
  exact LinearMap.congr_fun (boundary_subdivisionAlong φ) p

omit [LinearOrder ι] in
/-- Applying `d_*` to an elementary path again gives an elementary path. -/
theorem mapDPath_elementary_mem {B : Type*} [AddCommGroup B]
    (d : Configuration ι G →+ B)
    {p : Path (Configuration ι G) (Configuration ι G)}
    (hp : p ∈ elementaryPaths (ι := ι) (G := G)
      (X := Configuration ι G)) :
    mapDPath d p ∈ elementaryPaths (ι := ι) (G := G) (X := B) := by
  change p ∈ Submodule.span ℤ
    {q | ∃ (i : ι) (g : G) (x : Configuration ι G),
      g ≠ 0 ∧ q = edge (Finsupp.single i g) x} at hp
  induction hp using Submodule.span_induction with
  | mem p hp =>
      rcases hp with ⟨i, g, x, hg, rfl⟩
      rw [mapDPath_edge]
      exact elementaryEdge_mem i hg (d x)
  | zero => simp
  | add p q hp hq ihp ihq =>
      simpa using
        (Submodule.add_mem
          (elementaryPaths (ι := ι) (G := G) (X := B)) ihp ihq)
  | smul n p hp ih =>
      simpa using
        (Submodule.smul_mem
          (elementaryPaths (ι := ι) (G := G) (X := B)) n ih)

/-- `d_*` restricted to the elementary subgroups. -/
def mapDPathElementary {B : Type*} [AddCommGroup B]
    (d : Configuration ι G →+ B) :
    elementaryPaths (ι := ι) (G := G) (X := Configuration ι G) →ₗ[ℤ]
      elementaryPaths (ι := ι) (G := G) (X := B) :=
  LinearMap.codRestrict
    (elementaryPaths (ι := ι) (G := G) (X := B))
    ((mapDPath d).comp
      (elementaryPaths (ι := ι) (G := G)
        (X := Configuration ι G)).subtype)
    fun p => mapDPath_elementary_mem d p.property

omit [LinearOrder ι] in
@[simp]
theorem mapDPathElementary_coe {B : Type*} [AddCommGroup B]
    (d : Configuration ι G →+ B)
    (p : elementaryPaths (ι := ι) (G := G)
      (X := Configuration ι G)) :
    ((mapDPathElementary d p :
        elementaryPaths (ι := ι) (G := G) (X := B)) :
      Path (Configuration ι G) B) = mapDPath d p :=
  rfl

/-- Equation `d_* sd_pr = sd_cf d_*`, valued in elementary paths. -/
theorem mapDPathElementary_subdivisionElementary
    {B : Type*} [AddCommGroup B]
    (d : Configuration ι G →+ B) :
    (mapDPathElementary d).comp subdivisionElementary =
      (subdivisionAlongElementary d).comp (mapDPath d) := by
  apply LinearMap.ext
  intro p
  apply Subtype.ext
  change mapDPath d (subdivision p) =
    subdivisionAlong d (mapDPath d p)
  exact LinearMap.congr_fun (mapDPath_subdivision d) p

end GeneralSphereT.PathAlgebra
