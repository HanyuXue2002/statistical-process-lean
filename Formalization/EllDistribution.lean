import Formalization.SquareStrip
import Formalization.DistributionDifferences
import Formalization.LocalIdentity
import Formalization.IteratedLocality

set_option linter.style.header false

/-!
# Linearizing the square-strip error over base distributions

For a fixed edge `t` and a replacement word with the same endpoint, the map
`x ↦ ell φ t word x` extends linearly from point masses to arbitrary integral
distributions on the base group.  This file records that this linearization
commutes strictly with base translations and finite differences.  It is the
algebraic bridge used in the cone argument between local `tau`-identities and
the square-strip identity.
-/

noncomputable section

namespace GeneralSphereT.PathAlgebra

variable {I X : Type*} [AddCommGroup I] [AddCommGroup X]

/-- Translating every base point of a word path translates the whole path. -/
theorem baseTranslation_wordPath (φ : I →+ X) (word : List I)
    (u x : X) :
    baseTranslation u (wordPath φ word x) =
      wordPath φ word (x + u) := by
  induction word generalizing x with
  | nil => simp [wordPath]
  | cons r word ih =>
      simp only [wordPath, map_add, baseTranslation_edge, ih]
      congr 2
      ac_rfl

/-- The one-edge-minus-word error is equivariant under base translation. -/
theorem baseTranslation_ell (φ : I →+ X) (t : I) (word : List I)
    (u x : X) :
    baseTranslation u (ell φ t word x) =
      ell φ t word (x + u) := by
  simp [ell, baseTranslation_wordPath]

/-- Linear extension of `x ↦ ell φ t word x` to integral distributions. -/
def ellDistribution (φ : I →+ X) (t : I) (word : List I) :
    Dist X →ₗ[ℤ] Path I X :=
  Finsupp.linearCombination ℤ (ell φ t word)

@[simp]
theorem ellDistribution_single (φ : I →+ X) (t : I) (word : List I)
    (x : X) (n : ℤ) :
    ellDistribution φ t word (Finsupp.single x n) =
      n • ell φ t word x := by
  simp [ellDistribution]

/-- Linearized replacement commutes with translating the physical base. -/
theorem ellDistribution_distributionTranslation
    (φ : I →+ X) (t : I) (word : List I) (u : X) :
    (ellDistribution φ t word).comp (distributionTranslation u) =
      (baseTranslation u).comp (ellDistribution φ t word) := by
  ext x
  simp [baseTranslation_ell]

@[simp]
theorem ellDistribution_distributionTranslation_apply
    (φ : I →+ X) (t : I) (word : List I) (u : X) (z : Dist X) :
    ellDistribution φ t word (distributionTranslation u z) =
      baseTranslation u (ellDistribution φ t word z) :=
  LinearMap.congr_fun
    (ellDistribution_distributionTranslation φ t word u) z

/-- Consequently, linearized replacement commutes with finite differences. -/
theorem ellDistribution_distributionDifference
    (φ : I →+ X) (t : I) (word : List I) (u : X) :
    (ellDistribution φ t word).comp (distributionDifference u) =
      (baseDifference u).comp (ellDistribution φ t word) := by
  rw [distributionDifference, baseDifference]
  ext z
  simp only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.id_apply,
    map_sub, ellDistribution_distributionTranslation_apply]

@[simp]
theorem ellDistribution_distributionDifference_apply
    (φ : I →+ X) (t : I) (word : List I) (u : X) (z : Dist X) :
    ellDistribution φ t word (distributionDifference u z) =
      baseDifference u (ellDistribution φ t word z) :=
  LinearMap.congr_fun
    (ellDistribution_distributionDifference φ t word u) z

/-- On a one-step point difference, the linearized replacement error is
exactly the square strip minus the square swept by the original edge. -/
theorem ellDistribution_pointDifference
    (φ : I →+ X) (t : I) (word : List I) (r : I) (x : X)
    (hendpoint : φ (wordIncrement word) = φ t) :
    ellDistribution φ t word
        (distributionDifference (φ r) (Finsupp.single x 1)) =
      squareStrip φ word r x - square φ t r x := by
  rw [ellDistribution_distributionDifference_apply,
    ellDistribution_single]
  simp only [one_smul]
  exact squareStrip_identity φ t word r x hendpoint

/-- Base differences commute over any path increment type. -/
theorem baseDifference_commute_general (a b : X) (p : Path I X) :
    baseDifference a (baseDifference b p) =
      baseDifference b (baseDifference a p) := by
  let hmaps :
      (baseDifference (I := I) a).comp (baseDifference (I := I) b) =
        (baseDifference (I := I) b).comp (baseDifference (I := I) a) := by
    ext q
    change baseDifference a (baseDifference b (edge q.1 q.2)) =
      baseDifference b (baseDifference a (edge q.1 q.2))
    simp only [baseDifference_edge, map_sub]
    have hab : q.2 + b + a = q.2 + a + b := by abel
    rw [hab]
    abel
  exact LinearMap.congr_fun hmaps p

/-- One base difference commutes through a finite string of differences. -/
theorem baseDifference_iteratedBaseDifference_commute_general
    (φ : I →+ X) (r : I) (rs : List I) (p : Path I X) :
    baseDifference (φ r) (iteratedBaseDifference φ rs p) =
      iteratedBaseDifference φ rs (baseDifference (φ r) p) := by
  induction rs generalizing p with
  | nil => rfl
  | cons s rs ih =>
      simp only [iteratedBaseDifference_cons]
      rw [ih, baseDifference_commute_general]

/-- Linearized replacement carries a list of distribution differences to the
corresponding list of path-base differences. -/
theorem ellDistribution_iteratedDistributionDifference
    (φ : I →+ X) (t : I) (word : List I)
    (steps : List I) (z : Dist X) :
    ellDistribution φ t word
        (iteratedDistributionDifference (steps.map φ) z) =
      iteratedBaseDifference φ steps (ellDistribution φ t word z) := by
  induction steps generalizing z with
  | nil => rfl
  | cons r rs ih =>
      simp only [List.map_cons, iteratedDistributionDifference_cons,
        LinearMap.comp_apply, iteratedBaseDifference_cons]
      rw [ellDistribution_distributionDifference_apply, ih,
        baseDifference_iteratedBaseDifference_commute_general]

/-- The full elementary cube formula used in the simultaneous cone-operator
replacement: the first difference creates the square strip, and all remaining
differences act on it. -/
theorem ellDistribution_elementaryCube
    (φ : I →+ X) (t : I) (word : List I)
    (r : I) (rs : List I) (x : X)
    (hendpoint : φ (wordIncrement word) = φ t) :
    ellDistribution φ t word
        (iteratedDistributionDifference ((r :: rs).map φ)
          (Finsupp.single x 1)) =
      iteratedBaseDifference φ rs
        (squareStrip φ word r x - square φ t r x) := by
  rw [ellDistribution_iteratedDistributionDifference]
  simp only [iteratedBaseDifference_cons, ellDistribution_single, one_smul]
  congr 1
  change baseTranslation (φ r) (ell φ t word x) - ell φ t word x = _
  exact squareStrip_identity φ t word r x hendpoint

end GeneralSphereT.PathAlgebra
