import Formalization.CoordinateExtension
import Formalization.ReducedLocalKernel

set_option linter.style.header false

/-!
# Integral gluing of compatible reduced distributions

The nonzero Boolean cubes make the signed-distribution gluing statement
completely integral.  A local cube whose active coordinates lie in two
facets has one common coefficient; cubes lying in no facet are set to zero.
This file packages that construction independently of the Dold--Kan models.
-/

noncomputable section

namespace GeneralSphereT.PathAlgebra

universe uι uG uF

local instance classicalDecidableEq (X : Type*) : DecidableEq X :=
  Classical.decEq X

local instance classicalDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p

variable {ι : Type uι} {G : Type uG} [LinearOrder ι] [AddCommGroup G]
variable {Facet : Type uF} [Fintype Facet]

/-- Extend a nonzero local configuration by zero, retaining nonzeroness. -/
def extendNonzeroConfiguration (S : Set ι)
    (c : NonzeroConfiguration S G) : NonzeroConfiguration ι G :=
  ⟨coordinateExtension S c.1, by
    intro h
    have := congrArg (coordinateRestriction S) h
    have hc : c.1 = 0 := by simpa using this
    exact c.2 hc⟩

@[simp]
theorem extendNonzeroConfiguration_coe (S : Set ι)
    (c : NonzeroConfiguration S G) :
    (extendNonzeroConfiguration S c : Configuration ι G) =
      coordinateExtension S c.1 :=
  rfl

theorem extendNonzeroConfiguration_injective (S : Set ι) :
    Function.Injective (extendNonzeroConfiguration (G := G) S) := by
  intro a b h
  apply Subtype.ext
  have h' := congrArg
    (fun c : NonzeroConfiguration ι G =>
      coordinateRestriction S c.1) h
  simpa using h'

/-- A configuration supported in `S` is recovered by restriction followed
by extension by zero. -/
theorem coordinateExtension_coordinateRestriction_of_support_subset
    (S : Set ι) (c : Configuration ι G)
    (hc : ∀ i ∈ c.support, i ∈ S) :
    coordinateExtension S (coordinateRestriction S c) = c := by
  ext i
  by_cases hi : i ∈ S
  · simp [hi]
  · have hci : c i = 0 := by
      by_contra hne
      exact hi (hc i (Finsupp.mem_support_iff.mpr hne))
    simp [hi, hci]

/-- Restrict a nonzero ambient configuration known to be supported in `S`. -/
def restrictNonzeroConfiguration (S : Set ι)
    (c : NonzeroConfiguration ι G)
    (hc : ∀ i ∈ c.1.support, i ∈ S) : NonzeroConfiguration S G :=
  ⟨coordinateRestriction S c.1, by
    intro h
    have hext := congrArg (coordinateExtension S) h
    rw [coordinateExtension_coordinateRestriction_of_support_subset S c.1 hc]
      at hext
    exact c.2 hext⟩

@[simp]
theorem restrictNonzeroConfiguration_coe (S : Set ι)
    (c : NonzeroConfiguration ι G)
    (hc : ∀ i ∈ c.1.support, i ∈ S) :
    (restrictNonzeroConfiguration S c hc : Configuration S G) =
      coordinateRestriction S c.1 :=
  rfl

@[simp]
theorem restrict_extendNonzeroConfiguration (S : Set ι)
    (c : NonzeroConfiguration S G) :
    restrictNonzeroConfiguration S (extendNonzeroConfiguration S c)
        (by
          intro i hi
          by_contra hiS
          have hz := coordinateExtension_apply_not_mem S c.1 hiS
          exact (Finsupp.mem_support_iff.mp hi) hz) = c := by
  apply Subtype.ext
  exact coordinateRestriction_coordinateExtension S c.1

/-- A nonzero ambient cube is visible in at least one facet. -/
def CubeVisible (facets : Facet → Set ι)
    (c : NonzeroConfiguration ι G) : Prop :=
  ∃ ρ : Facet, ∀ i ∈ c.1.support, i ∈ facets ρ

/-- A chosen facet in which a visible cube survives. -/
def chosenCubeFacet (facets : Facet → Set ι)
    (c : NonzeroConfiguration ι G) (hc : CubeVisible facets c) : Facet :=
  Classical.choose hc

theorem support_subset_chosenCubeFacet (facets : Facet → Set ι)
    (c : NonzeroConfiguration ι G) (hc : CubeVisible facets c) :
    ∀ i ∈ c.1.support, i ∈ facets (chosenCubeFacet facets c hc) :=
  Classical.choose_spec hc

/-- Cube-coordinate compatibility is the exact hypothesis needed for
integral gluing. -/
def CubeCoefficientCompatible (facets : Facet → Set ι)
    (u : ∀ ρ : Facet, RedDist (Configuration (facets ρ) G)) : Prop :=
  ∀ (c : NonzeroConfiguration ι G) (ρ σ : Facet)
      (hρ : ∀ i ∈ c.1.support, i ∈ facets ρ)
      (hσ : ∀ i ∈ c.1.support, i ∈ facets σ),
    (reducedCubeBasis (G := G)).repr (u ρ)
        (restrictNonzeroConfiguration (facets ρ) c hρ) =
      (reducedCubeBasis (G := G)).repr (u σ)
        (restrictNonzeroConfiguration (facets σ) c hσ)

/-- The finite set containing every global cube that can receive a nonzero
coefficient from one of the local distributions. -/
def gluedCubeSupport (facets : Facet → Set ι)
    (u : ∀ ρ : Facet, RedDist (Configuration (facets ρ) G)) :
    Finset (NonzeroConfiguration ι G) :=
  Finset.univ.biUnion fun ρ =>
    ((reducedCubeBasis (G := G)).repr (u ρ)).support.image
      (extendNonzeroConfiguration (G := G) (facets ρ))

/-- The common coefficient of a visible cube, read in a chosen facet. -/
def gluedCubeCoefficient (facets : Facet → Set ι)
    (u : ∀ ρ : Facet, RedDist (Configuration (facets ρ) G))
    (c : NonzeroConfiguration ι G) : ℤ :=
  if hc : CubeVisible facets c then
    (reducedCubeBasis (G := G)).repr
      (u (chosenCubeFacet facets c hc))
      (restrictNonzeroConfiguration
        (facets (chosenCubeFacet facets c hc)) c
        (support_subset_chosenCubeFacet facets c hc))
  else 0

theorem gluedCubeCoefficient_eq_of_visible
    (facets : Facet → Set ι)
    (u : ∀ ρ : Facet, RedDist (Configuration (facets ρ) G))
    (hu : CubeCoefficientCompatible facets u)
    (c : NonzeroConfiguration ι G) (ρ : Facet)
    (hρ : ∀ i ∈ c.1.support, i ∈ facets ρ) :
    gluedCubeCoefficient facets u c =
      (reducedCubeBasis (G := G)).repr (u ρ)
        (restrictNonzeroConfiguration (facets ρ) c hρ) := by
  let hc : CubeVisible facets c := ⟨ρ, hρ⟩
  classical
  simp only [gluedCubeCoefficient, dif_pos hc]
  exact hu c (chosenCubeFacet facets c hc) ρ
    (support_subset_chosenCubeFacet facets c hc) hρ

/-- The common cube coefficients as a finitely supported function. -/
def gluedCubeCoordinates (facets : Facet → Set ι)
    (u : ∀ ρ : Facet, RedDist (Configuration (facets ρ) G)) :
    NonzeroConfiguration ι G →₀ ℤ :=
  Finsupp.onFinset (gluedCubeSupport facets u)
    (gluedCubeCoefficient facets u) (by
      intro c hcoeff
      by_cases hvis : CubeVisible facets c
      · let ρ := chosenCubeFacet facets c hvis
        let hρ := support_subset_chosenCubeFacet facets c hvis
        let a := restrictNonzeroConfiguration (facets ρ) c hρ
        have ha : a ∈
            ((reducedCubeBasis (G := G)).repr (u ρ)).support := by
          apply Finsupp.mem_support_iff.mpr
          simpa only [gluedCubeCoefficient, dif_pos hvis] using hcoeff
        unfold gluedCubeSupport
        refine Finset.mem_biUnion.mpr ⟨ρ, Finset.mem_univ _, ?_⟩
        apply Finset.mem_image.mpr
        refine ⟨a, ha, ?_⟩
        apply Subtype.ext
        exact coordinateExtension_coordinateRestriction_of_support_subset
          (facets ρ) c.1 hρ
      · have : gluedCubeCoefficient facets u c = 0 := by
          simp only [gluedCubeCoefficient, dif_neg hvis]
        exact (hcoeff this).elim)

/-- Synthesize the global reduced distribution from the common cube
coefficients. -/
def glueReducedDistributions (facets : Facet → Set ι)
    (u : ∀ ρ : Facet, RedDist (Configuration (facets ρ) G)) :
    RedDist (Configuration ι G) :=
  nonzeroCubeSynthesis (gluedCubeCoordinates facets u)

@[simp]
theorem reducedCubeBasis_repr_glueReducedDistributions
    (facets : Facet → Set ι)
    (u : ∀ ρ : Facet, RedDist (Configuration (facets ρ) G)) :
    (reducedCubeBasis (G := G)).repr
        (glueReducedDistributions facets u) =
      gluedCubeCoordinates facets u := by
  change (nonzeroCubeLinearEquiv (G := G)).symm
      (nonzeroCubeSynthesis (gluedCubeCoordinates facets u)) = _
  exact (nonzeroCubeLinearEquiv (G := G)).symm_apply_apply _

theorem gluedCubeCoordinates_apply_of_visible
    (facets : Facet → Set ι)
    (u : ∀ ρ : Facet, RedDist (Configuration (facets ρ) G))
    (hu : CubeCoefficientCompatible facets u)
    (c : NonzeroConfiguration ι G) (ρ : Facet)
    (hρ : ∀ i ∈ c.1.support, i ∈ facets ρ) :
    gluedCubeCoordinates facets u c =
      (reducedCubeBasis (G := G)).repr (u ρ)
        (restrictNonzeroConfiguration (facets ρ) c hρ) := by
  rw [gluedCubeCoordinates, Finsupp.onFinset_apply]
  exact gluedCubeCoefficient_eq_of_visible facets u hu c ρ hρ

/-- The synthesized global distribution has the prescribed restriction on
every facet. -/
theorem mapRedDist_glueReducedDistributions
    (facets : Facet → Set ι)
    (u : ∀ ρ : Facet, RedDist (Configuration (facets ρ) G))
    (hu : CubeCoefficientCompatible facets u) (ρ : Facet) :
    mapRedDist (coordinateRestriction (facets ρ))
        (glueReducedDistributions facets u) = u ρ := by
  apply (reducedCubeBasis (G := G)).repr.injective
  ext a
  let c := extendNonzeroConfiguration (G := G) (facets ρ) a
  let hc : ∀ i ∈ c.1.support, i ∈ facets ρ := by
    intro i hi
    by_contra hiρ
    have hz := coordinateExtension_apply_not_mem (facets ρ) a.1 hiρ
    exact (Finsupp.mem_support_iff.mp hi) hz
  rw [reducedCube_repr_eq_cubeCoefficient,
    reducedCube_repr_eq_cubeCoefficient]
  have hcoeff := LinearMap.congr_fun
    (cubeCoefficient_mapDist_coordinateRestriction (G := G)
      (facets ρ) c.1 hc)
    (glueReducedDistributions facets u).1
  simp only [LinearMap.comp_apply] at hcoeff
  have hrest : coordinateRestriction (facets ρ) c.1 = a.1 :=
    coordinateRestriction_coordinateExtension (facets ρ) a.1
  change cubeCoefficient a.1
      (mapDist (coordinateRestriction (facets ρ))
        (glueReducedDistributions facets u).1) =
      cubeCoefficient a.1 (u ρ).1
  rw [← hrest, hcoeff]
  rw [← reducedCube_repr_eq_cubeCoefficient c
      (glueReducedDistributions facets u)]
  rw [show (reducedCubeBasis (G := G)).repr
      (glueReducedDistributions facets u) c =
        gluedCubeCoordinates facets u c by
      exact DFunLike.congr_fun
        (reducedCubeBasis_repr_glueReducedDistributions facets u) c]
  rw [gluedCubeCoordinates_apply_of_visible facets u hu c ρ hc]
  rw [reducedCube_repr_eq_cubeCoefficient]
  have hlocal := restrict_extendNonzeroConfiguration
    (G := G) (facets ρ) a
  rw [hlocal]
  rw [hrest]

end GeneralSphereT.PathAlgebra
