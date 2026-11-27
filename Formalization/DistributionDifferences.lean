import Formalization.CubeBasis

set_option linter.style.header false

/-!
# Finite differences on arbitrary free distributions

This module separates the finite-difference calculation used in
Lemma 2.25 from the configuration group ring.  Translation and difference are
defined on `Dist X` for every additive commutative group `X`; iterating them is
strictly natural under additive maps.  The final theorem identifies the image
of the cube distribution with the iterated differences of its active
coordinate increments.
-/

noncomputable section

namespace GeneralSphereT.PathAlgebra

section ArbitraryDifferences

variable {X Y : Type*} [AddCommGroup X] [AddCommGroup Y]

/-- Translation by `a` on the free integral distributions on `X`. -/
def distributionTranslation (a : X) : Dist X →ₗ[ℤ] Dist X :=
  Finsupp.linearCombination ℤ fun x => Finsupp.single (x + a) 1

@[simp]
theorem distributionTranslation_single (a x : X) (n : ℤ) :
    distributionTranslation a (Finsupp.single x n) =
      Finsupp.single (x + a) n := by
  simp [distributionTranslation]

/-- The raw finite difference `T_a - 1` on free distributions. -/
def distributionDifference (a : X) : Dist X →ₗ[ℤ] Dist X :=
  distributionTranslation a - LinearMap.id

@[simp]
theorem distributionDifference_single (a x : X) (n : ℤ) :
    distributionDifference a (Finsupp.single x n) =
      Finsupp.single (x + a) n - Finsupp.single x n := by
  simp [distributionDifference]

/-- Pushforward strictly commutes with translation. -/
theorem mapDist_distributionTranslation (f : X →+ Y) (a : X) :
    (mapDist f).comp (distributionTranslation a) =
      (distributionTranslation (f a)).comp (mapDist f) := by
  ext x
  simp [add_comm]

/-- Pushforward strictly commutes with the finite difference `T_a - 1`. -/
theorem mapDist_distributionDifference (f : X →+ Y) (a : X) :
    (mapDist f).comp (distributionDifference a) =
      (distributionDifference (f a)).comp (mapDist f) := by
  rw [distributionDifference, distributionDifference]
  ext x
  simp

/-- Apply the finite differences in a finite list, from right to left. -/
def iteratedDistributionDifference : List X → Dist X →ₗ[ℤ] Dist X
  | [] => LinearMap.id
  | a :: steps =>
      (distributionDifference a).comp
        (iteratedDistributionDifference steps)

@[simp]
theorem iteratedDistributionDifference_nil :
    iteratedDistributionDifference ([] : List X) = LinearMap.id := by
  rfl

@[simp]
theorem iteratedDistributionDifference_cons (a : X) (steps : List X) :
    iteratedDistributionDifference (a :: steps) =
      (distributionDifference a).comp
        (iteratedDistributionDifference steps) := by
  rfl

/-- Naturality of every finite string of differences. -/
theorem mapDist_iteratedDistributionDifference
    (f : X →+ Y) (steps : List X) :
    (mapDist f).comp (iteratedDistributionDifference steps) =
      (iteratedDistributionDifference (steps.map f)).comp (mapDist f) := by
  induction steps with
  | nil => rfl
  | cons a steps ih =>
      simp only [iteratedDistributionDifference_cons, List.map_cons,
        LinearMap.comp_assoc]
      rw [← ih]
      rw [← LinearMap.comp_assoc, mapDist_distributionDifference]
      rw [LinearMap.comp_assoc]

@[simp]
theorem mapDist_iteratedDistributionDifference_apply
    (f : X →+ Y) (steps : List X) (u : Dist X) :
    mapDist f (iteratedDistributionDifference steps u) =
      iteratedDistributionDifference (steps.map f) (mapDist f u) := by
  exact LinearMap.congr_fun
    (mapDist_iteratedDistributionDifference f steps) u

end ArbitraryDifferences

section CubeBridge

variable {ι G X : Type*} [LinearOrder ι] [AddCommGroup G]
  [AddCommGroup X]

/-- The list of active one-coordinate increments of `c`. -/
def activeCoordinateIncrements (c : Configuration ι G) :
    List (Configuration ι G) :=
  c.support.toList.map fun i => Finsupp.single i (c i)

omit [LinearOrder ι] in
theorem distributionDifference_eq_differenceDistribution
    (a : Configuration ι G) :
    distributionDifference a = differenceDistribution a := by
  rfl

omit [LinearOrder ι] in
/-- Under the coefficient/group-ring equivalence, iterated differences become
the corresponding product of the factors `delta a - 1`. -/
theorem distributionToRing_iteratedDistributionDifference
    (steps : List (Configuration ι G))
    (u : Dist (Configuration ι G)) :
    distributionToRing (iteratedDistributionDifference steps u) =
      (steps.map fun a => delta a - 1).prod * distributionToRing u := by
  induction steps with
  | nil => simp
  | cons a steps ih =>
      rw [iteratedDistributionDifference_cons, LinearMap.comp_apply,
        distributionDifference_eq_differenceDistribution,
        distributionToRing_difference, ih]
      simp only [List.map_cons, List.prod_cons]
      noncomm_ring

omit [LinearOrder ι] in
/-- The existing cube distribution is literally the iterated raw difference
of its active coordinate increments, applied to the point mass at zero. -/
theorem cubeDistribution_eq_iteratedDistributionDifference
    (c : Configuration ι G) :
    cubeDistribution c =
      iteratedDistributionDifference (activeCoordinateIncrements c)
        (Finsupp.single 0 1) := by
  apply (AddMonoidAlgebra.coeffLinearEquiv ℤ).symm.injective
  change distributionToRing (cubeDistribution c) =
    distributionToRing
      (iteratedDistributionDifference (activeCoordinateIncrements c)
        (Finsupp.single 0 1))
  rw [distributionToRing_iteratedDistributionDifference]
  simp only [activeCoordinateIncrements, List.map_map,
    distributionToRing_single]
  rw [show AddMonoidAlgebra.single (0 : Configuration ι G) (1 : ℤ) = 1 by
    change delta (0 : Configuration ι G) = 1
    exact delta_zero]
  rw [mul_one]
  change cube c = _
  rw [cube, cubeOn]
  simp

omit [LinearOrder ι] in
/-- Formula used in Lemma 2.25: after applying an additive map, `Q(c)` is the
iterated raw difference by the images of all active coordinate increments. -/
theorem mapDist_cubeDistribution_eq_iteratedDistributionDifference
    (f : Configuration ι G →+ X) (c : Configuration ι G) :
    mapDist f (cubeDistribution c) =
      iteratedDistributionDifference
        (c.support.toList.map fun i => f (Finsupp.single i (c i)))
        (Finsupp.single 0 1) := by
  rw [cubeDistribution_eq_iteratedDistributionDifference]
  rw [mapDist_iteratedDistributionDifference_apply]
  rw [mapDist_single, map_zero]
  simp only [activeCoordinateIncrements, List.map_map, Function.comp_def]

end CubeBridge

end GeneralSphereT.PathAlgebra
