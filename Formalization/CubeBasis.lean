import Formalization.Subdivision
import Mathlib.LinearAlgebra.Finsupp.VectorSpace

set_option linter.style.header false

/-!
# A Boolean cube basis for finitely supported configurations

This module gives a direct replacement for the tensor-product change of basis
around equation (2.19).  The free distribution group is viewed as
the integral group ring of the additive configuration group.  In that ring,
translation by `a` is multiplication by `delta a`, so the finite difference
`T_a - 1` is multiplication by `delta a - 1`.

For a configuration `c`, `cube c` is the product of these differences over
the active coordinates of `c`.  Boolean expansion and Möbius inversion show
that these cubes form an integral basis indexed by configurations.
-/

noncomputable section

open scoped BigOperators

namespace GeneralSphereT.PathAlgebra

section CubeBasis

variable {ι G : Type*} [LinearOrder ι] [AddCommGroup G]

/-- The integral group ring of the additive configuration group. -/
abbrev ConfigurationRing (ι G : Type*) [AddMonoid G] :=
  AddMonoidAlgebra ℤ (Configuration ι G)

/-- The group-ring basis vector at a configuration. -/
def delta (c : Configuration ι G) : ConfigurationRing ι G :=
  AddMonoidAlgebra.single c 1

omit [LinearOrder ι] in
@[simp]
theorem delta_zero : delta (0 : Configuration ι G) = 1 := by
  rfl

omit [LinearOrder ι] in
@[simp]
theorem delta_mul_delta (a b : Configuration ι G) :
    delta a * delta b = delta (a + b) := by
  simp [delta]

/-- Translation of an actual free distribution. -/
def translateDistribution (a : Configuration ι G) :
    Dist (Configuration ι G) →ₗ[ℤ] Dist (Configuration ι G) :=
  Finsupp.linearCombination ℤ fun x => Finsupp.single (x + a) 1

omit [LinearOrder ι] in
@[simp]
theorem translateDistribution_single
    (a x : Configuration ι G) (n : ℤ) :
    translateDistribution a (Finsupp.single x n) =
      Finsupp.single (x + a) n := by
  simp [translateDistribution]

/-- The finite-difference operator `T_a - 1` on free distributions. -/
def differenceDistribution (a : Configuration ι G) :
    Dist (Configuration ι G) →ₗ[ℤ] Dist (Configuration ι G) :=
  translateDistribution a - LinearMap.id

omit [LinearOrder ι] in
@[simp]
theorem differenceDistribution_single
    (a x : Configuration ι G) (n : ℤ) :
    differenceDistribution a (Finsupp.single x n) =
      Finsupp.single (x + a) n - Finsupp.single x n := by
  simp [differenceDistribution]

/-- Regard a free distribution as an element of the configuration group ring. -/
def distributionToRing :
    Dist (Configuration ι G) →ₗ[ℤ] ConfigurationRing ι G :=
  (AddMonoidAlgebra.coeffLinearEquiv ℤ).symm.toLinearMap

omit [LinearOrder ι] in
@[simp]
theorem distributionToRing_single (x : Configuration ι G) (n : ℤ) :
    distributionToRing (Finsupp.single x n) =
      AddMonoidAlgebra.single x n := by
  simp [distributionToRing]

omit [LinearOrder ι] in
@[simp]
theorem coeff_distributionToRing (u : Dist (Configuration ι G)) :
    (distributionToRing u).coeff = u := by
  simp [distributionToRing]

omit [LinearOrder ι] in
/-- The concrete translation above is multiplication by `delta a` in the group ring. -/
theorem distributionToRing_translate
    (a : Configuration ι G) (u : Dist (Configuration ι G)) :
    distributionToRing (translateDistribution a u) =
      delta a * distributionToRing u := by
  classical
  induction u using Finsupp.induction with
  | zero => simp
  | single_add x n u _ _ ih =>
      simp only [map_add, translateDistribution_single,
        distributionToRing_single, ih, mul_add]
      simp [delta, add_comm]

omit [LinearOrder ι] in
/-- Consequently, `T_a - 1` really is multiplication by `delta a - 1`. -/
theorem distributionToRing_difference
    (a : Configuration ι G) (u : Dist (Configuration ι G)) :
    distributionToRing (differenceDistribution a u) =
      (delta a - 1) * distributionToRing u := by
  rw [differenceDistribution]
  simp only [LinearMap.sub_apply, LinearMap.id_apply, map_sub,
    distributionToRing_translate]
  noncomm_ring

/-- Translation in the group-ring model of distributions. -/
def ringTranslate (a : Configuration ι G) (u : ConfigurationRing ι G) :
    ConfigurationRing ι G :=
  delta a * u

/-- Finite difference in the group-ring model of distributions. -/
def ringDifference (a : Configuration ι G) (u : ConfigurationRing ι G) :
    ConfigurationRing ι G :=
  ringTranslate a u - u

omit [LinearOrder ι] in
@[simp]
theorem ringTranslate_delta (a x : Configuration ι G) :
    ringTranslate a (delta x) = delta (a + x) := by
  simp [ringTranslate]

omit [LinearOrder ι] in
@[simp]
theorem ringDifference_delta (a x : Configuration ι G) :
    ringDifference a (delta x) = delta (a + x) - delta x := by
  simp [ringDifference, ringTranslate]

omit [LinearOrder ι] in
@[simp]
theorem ringDifference_one (a : Configuration ι G) :
    ringDifference a 1 = delta a - 1 := by
  simp [ringDifference, ringTranslate]

/-- Keep only the coordinates belonging to `s`. -/
def coordinateTruncation (c : Configuration ι G) (s : Finset ι) :
    Configuration ι G :=
  ∑ i ∈ s, Finsupp.single i (c i)

omit [LinearOrder ι] in
@[simp]
theorem coordinateTruncation_empty (c : Configuration ι G) :
    coordinateTruncation c ∅ = 0 := by
  simp [coordinateTruncation]

@[simp]
theorem coordinateTruncation_apply
    (c : Configuration ι G) (s : Finset ι) (i : ι) :
    coordinateTruncation c s i = if i ∈ s then c i else 0 := by
  classical
  simp [coordinateTruncation, Finsupp.single_apply]

theorem coordinateTruncation_support (c : Configuration ι G) :
    coordinateTruncation c c.support = c := by
  ext i
  simp [coordinateTruncation_apply]

theorem support_coordinateTruncation
    (c : Configuration ι G) {s : Finset ι} (hs : s ⊆ c.support) :
    (coordinateTruncation c s).support = s := by
  ext i
  by_cases hi : i ∈ s
  · have hci : c i ≠ 0 := by
      simpa using hs hi
    simp [coordinateTruncation_apply, hi, hci]
  · simp [coordinateTruncation_apply, hi]

theorem coordinateTruncation_coordinateTruncation
    (c : Configuration ι G) {s t : Finset ι} (hts : t ⊆ s) :
    coordinateTruncation (coordinateTruncation c s) t =
      coordinateTruncation c t := by
  ext i
  by_cases hi : i ∈ t
  · have his : i ∈ s := hts hi
    simp [coordinateTruncation_apply, hi, his]
  · simp [coordinateTruncation_apply, hi]

/-- Multiplying basis vectors adds their configurations coordinatewise. -/
theorem prod_delta_coordinateTruncation
    (c : Configuration ι G) (s : Finset ι) :
    (∏ i ∈ s, delta (Finsupp.single i (c i))) =
      delta (coordinateTruncation c s) := by
  classical
  induction s using Finset.induction with
  | empty => simp [coordinateTruncation]
  | @insert i s hi ih =>
      simp [coordinateTruncation, hi, ih]

/-- The product of coordinate differences over an arbitrary finite set. -/
def cubeOn (c : Configuration ι G) (s : Finset ι) :
    ConfigurationRing ι G :=
  ∏ i ∈ s, (delta (Finsupp.single i (c i)) - 1)

/-- The cube attached to a configuration uses precisely its active coordinates. -/
def cube (c : Configuration ι G) : ConfigurationRing ι G :=
  cubeOn c c.support

omit [LinearOrder ι] in
/-- Literal form of `Q(c)=∏_i (T_{c_i}-1)[0]` in the group-ring model. -/
theorem cube_eq_prod_coordinate_differences (c : Configuration ι G) :
    cube c =
      ∏ i ∈ c.support,
        ringDifference (Finsupp.single i (c i)) 1 := by
  simp [cube, cubeOn]

omit [LinearOrder ι] in
@[simp]
theorem cube_zero : cube (0 : Configuration ι G) = 1 := by
  simp [cube, cubeOn]

/--
Boolean expansion of a product of finite differences.  A subset `t` records
the factors in which the `-1` term was selected.
-/
theorem cubeOn_expansion (c : Configuration ι G) (s : Finset ι) :
    cubeOn c s =
      ∑ t ∈ s.powerset,
        (-1 : ConfigurationRing ι G) ^ t.card *
          delta (coordinateTruncation c (s \ t)) := by
  classical
  rw [cubeOn, Finset.prod_sub]
  apply Finset.sum_congr rfl
  intro t ht
  rw [prod_delta_coordinateTruncation]
  simp

/-- The expansion specialized to the active coordinates of `c`. -/
theorem cube_expansion (c : Configuration ι G) :
    cube c =
      ∑ t ∈ c.support.powerset,
        (-1 : ConfigurationRing ι G) ^ t.card *
          delta (coordinateTruncation c (c.support \ t)) := by
  exact cubeOn_expansion c c.support

omit [LinearOrder ι] in
/-- A sign in the coefficient ring only changes the coefficient of a basis vector. -/
theorem neg_one_pow_mul_delta (n : ℕ) (x : Configuration ι G) :
    (-1 : ConfigurationRing ι G) ^ n * delta x =
      AddMonoidAlgebra.single x ((-1 : ℤ) ^ n) := by
  induction n with
  | zero => simp [delta]
  | succ n ih =>
      calc
        (-1 : ConfigurationRing ι G) ^ (n + 1) * delta x =
            (-1 : ConfigurationRing ι G) *
              ((-1 : ConfigurationRing ι G) ^ n * delta x) := by
          ring
        _ = (-1 : ConfigurationRing ι G) *
              AddMonoidAlgebra.single x ((-1 : ℤ) ^ n) := by rw [ih]
        _ = AddMonoidAlgebra.single x ((-1 : ℤ) ^ (n + 1)) := by
          simp [pow_succ, mul_comm]

/--
Boolean Mobius inversion before specializing to the support of a
configuration.
-/
theorem cubeOn_mobius_inversion
    (c : Configuration ι G) (s : Finset ι) :
    ∑ t ∈ s.powerset, cubeOn c t =
      delta (coordinateTruncation c s) := by
  classical
  simp only [cubeOn]
  rw [← Finset.prod_add_one]
  simp only [sub_add_cancel]
  exact prod_delta_coordinateTruncation c s

/-- Restricting a configuration and then forming its cube changes no factor. -/
theorem cube_coordinateTruncation
    (c : Configuration ι G) {s : Finset ι} (hs : s ⊆ c.support) :
    cube (coordinateTruncation c s) = cubeOn c s := by
  classical
  rw [cube, support_coordinateTruncation c hs]
  apply Finset.prod_congr rfl
  intro i hi
  simp [coordinateTruncation_apply, hi]

/--
The desired cube-basis inversion: every configuration basis vector is the sum
of the cubes attached to all of its coordinate restrictions.
-/
theorem cube_mobius_inversion (c : Configuration ι G) :
    delta c =
      ∑ s ∈ c.support.powerset, cube (coordinateTruncation c s) := by
  classical
  calc
    delta c = delta (coordinateTruncation c c.support) := by
      rw [coordinateTruncation_support]
    _ = ∑ s ∈ c.support.powerset, cubeOn c s :=
      (cubeOn_mobius_inversion c c.support).symm
    _ = ∑ s ∈ c.support.powerset, cube (coordinateTruncation c s) := by
      apply Finset.sum_congr rfl
      intro s hs
      rw [cube_coordinateTruncation c (Finset.mem_powerset.mp hs)]

/-- The cube as an element of the paper's free distribution group. -/
def cubeDistribution (c : Configuration ι G) :
    Dist (Configuration ι G) :=
  (cube c).coeff

/-- The Boolean expansion written entirely in the paper's free distribution group. -/
theorem cubeDistribution_expansion (c : Configuration ι G) :
    cubeDistribution c =
      ∑ t ∈ c.support.powerset,
        Finsupp.single (coordinateTruncation c (c.support \ t))
          ((-1 : ℤ) ^ t.card) := by
  rw [cubeDistribution, cube_expansion]
  simp only [AddMonoidAlgebra.coeff_sum]
  apply Finset.sum_congr rfl
  intro t ht
  rw [neg_one_pow_mul_delta]
  rfl

/-- The ring-level inversion immediately gives an identity of free distributions. -/
theorem cubeDistribution_mobius_inversion (c : Configuration ι G) :
    Finsupp.single c 1 =
      ∑ s ∈ c.support.powerset,
        cubeDistribution (coordinateTruncation c s) := by
  have h := congrArg AddMonoidAlgebra.coeff (cube_mobius_inversion c)
  simpa [cubeDistribution, delta] using h

/--
Boolean inclusion--exclusion in a form tailored to the inverse composition.
For each `t`, first omit the coordinates in `t` and then sum over every
subset of those that remain.
-/
theorem boolean_inclusion_exclusion
    {A : Type*} [AddCommGroup A] (F : Finset ι → A) (s : Finset ι) :
    (∑ t ∈ s.powerset,
        ((-1 : ℤ) ^ t.card) •
          ∑ u ∈ (s \ t).powerset, F u) =
      F s := by
  classical
  induction s using Finset.induction generalizing F with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.sum_powerset_insert ha]
      have hfirst :
          (∑ t ∈ s.powerset,
              ((-1 : ℤ) ^ t.card) •
                ∑ u ∈ ((insert a s) \ t).powerset, F u) =
            (∑ t ∈ s.powerset,
                ((-1 : ℤ) ^ t.card) •
                  ∑ u ∈ (s \ t).powerset, F u) +
              ∑ t ∈ s.powerset,
                ((-1 : ℤ) ^ t.card) •
                  ∑ u ∈ (s \ t).powerset, F (insert a u) := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro t ht
        have hat : a ∉ t := by
          intro hat
          exact ha (Finset.mem_powerset.mp ht hat)
        have hdiff : (insert a s) \ t = insert a (s \ t) := by
          ext i
          simp only [Finset.mem_sdiff, Finset.mem_insert]
          constructor
          · rintro ⟨hi | his, hit⟩
            · exact Or.inl hi
            · exact Or.inr ⟨his, hit⟩
          · rintro (rfl | ⟨his, hit⟩)
            · exact ⟨Or.inl rfl, hat⟩
            · exact ⟨Or.inr his, hit⟩
        have hadiff : a ∉ s \ t := by
          simp [ha]
        rw [hdiff, Finset.sum_powerset_insert hadiff, smul_add]
      have hsecond :
          (∑ t ∈ s.powerset,
              ((-1 : ℤ) ^ (insert a t).card) •
                ∑ u ∈ ((insert a s) \ insert a t).powerset, F u) =
            -∑ t ∈ s.powerset,
              ((-1 : ℤ) ^ t.card) •
                ∑ u ∈ (s \ t).powerset, F u := by
        rw [← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro t ht
        have hat : a ∉ t := by
          intro hat
          exact ha (Finset.mem_powerset.mp ht hat)
        have hdiff : (insert a s) \ insert a t = s \ t := by
          ext i
          simp only [Finset.mem_sdiff, Finset.mem_insert, not_or]
          constructor
          · rintro ⟨hi, hia, hit⟩
            rcases hi with hi | his
            · exact (hia hi).elim
            · exact ⟨his, hit⟩
          · rintro ⟨his, hit⟩
            have hia : ¬i = a := by
              intro hia
              subst i
              exact ha his
            exact ⟨Or.inr his, hia, hit⟩
        rw [hdiff, Finset.card_insert_of_notMem hat]
        simp [pow_succ]
      rw [hfirst, hsecond, ih (F := fun u => F (insert a u))]
      abel

/-- Linear extension sending the ordinary basis vector at `c` to its cube. -/
def cubeTransform :
    Dist (Configuration ι G) →ₗ[ℤ] Dist (Configuration ι G) :=
  Finsupp.linearCombination ℤ cubeDistribution

omit [LinearOrder ι] in
@[simp]
theorem cubeTransform_single (c : Configuration ι G) (n : ℤ) :
    cubeTransform (Finsupp.single c n) = n • cubeDistribution c := by
  simp [cubeTransform]

/-- Sum of all coordinate restrictions of a configuration. -/
def subsetDistribution (c : Configuration ι G) :
    Dist (Configuration ι G) :=
  ∑ s ∈ c.support.powerset,
    Finsupp.single (coordinateTruncation c s) 1

/-- Linear extension of the Boolean subset-sum operation. -/
def subsetSumTransform :
    Dist (Configuration ι G) →ₗ[ℤ] Dist (Configuration ι G) :=
  Finsupp.linearCombination ℤ subsetDistribution

omit [LinearOrder ι] in
@[simp]
theorem subsetSumTransform_single (c : Configuration ι G) (n : ℤ) :
    subsetSumTransform (Finsupp.single c n) = n • subsetDistribution c := by
  simp [subsetSumTransform]

/-- The subset sum of a truncation is indexed by the same ambient subsets. -/
theorem subsetDistribution_coordinateTruncation
    (c : Configuration ι G) {s : Finset ι} (hs : s ⊆ c.support) :
    subsetDistribution (coordinateTruncation c s) =
      ∑ u ∈ s.powerset,
        Finsupp.single (coordinateTruncation c u) 1 := by
  rw [subsetDistribution, support_coordinateTruncation c hs]
  apply Finset.sum_congr rfl
  intro u hu
  rw [coordinateTruncation_coordinateTruncation c
    (Finset.mem_powerset.mp hu)]

/-- The subset-sum transform also undoes each cube. -/
theorem subsetSumTransform_cubeDistribution (c : Configuration ι G) :
    subsetSumTransform (cubeDistribution c) = Finsupp.single c 1 := by
  rw [cubeDistribution_expansion, map_sum]
  simp only [subsetSumTransform_single]
  calc
    (∑ t ∈ c.support.powerset,
        ((-1 : ℤ) ^ t.card) •
          subsetDistribution
            (coordinateTruncation c (c.support \ t))) =
        ∑ t ∈ c.support.powerset,
          ((-1 : ℤ) ^ t.card) •
            ∑ u ∈ (c.support \ t).powerset,
              Finsupp.single (coordinateTruncation c u) 1 := by
      apply Finset.sum_congr rfl
      intro t ht
      rw [subsetDistribution_coordinateTruncation c Finset.sdiff_subset]
    _ = Finsupp.single (coordinateTruncation c c.support) 1 := by
      exact boolean_inclusion_exclusion
        (fun u => Finsupp.single (coordinateTruncation c u) 1) c.support
    _ = Finsupp.single c 1 := by
      rw [coordinateTruncation_support]

/-- Mobius inversion says that the cube transform undoes every subset sum. -/
theorem cubeTransform_subsetDistribution (c : Configuration ι G) :
    cubeTransform (subsetDistribution c) = Finsupp.single c 1 := by
  rw [subsetDistribution, map_sum]
  simp only [cubeTransform_single, one_smul]
  exact (cubeDistribution_mobius_inversion c).symm

/-- Thus the cube transform has an explicit right inverse over the integers. -/
theorem cubeTransform_comp_subsetSumTransform :
    (cubeTransform (ι := ι) (G := G)).comp
        (subsetSumTransform (ι := ι) (G := G)) =
      LinearMap.id (R := ℤ) (M := Dist (Configuration ι G)) := by
  ext c
  simp [subsetSumTransform, cubeTransform_subsetDistribution]

/-- The inverse composition, proved by Boolean inclusion--exclusion. -/
theorem subsetSumTransform_comp_cubeTransform :
    (subsetSumTransform (ι := ι) (G := G)).comp
        (cubeTransform (ι := ι) (G := G)) =
      LinearMap.id (R := ℤ) (M := Dist (Configuration ι G)) := by
  ext c
  simp [cubeTransform, subsetSumTransform_cubeDistribution]

/-- The integral change from point masses to cubes is a linear equivalence. -/
def cubeLinearEquiv :
    Dist (Configuration ι G) ≃ₗ[ℤ] Dist (Configuration ι G) :=
  LinearEquiv.ofLinearMap
    (cubeTransform (ι := ι) (G := G))
    (subsetSumTransform (ι := ι) (G := G))
    (cubeTransform_comp_subsetSumTransform (ι := ι) (G := G))
    (subsetSumTransform_comp_cubeTransform (ι := ι) (G := G))

/-- The cubes form an honest integral basis indexed by configurations. -/
def cubeBasis :
    Module.Basis (Configuration ι G) ℤ (Dist (Configuration ι G)) :=
  Finsupp.basisSingleOne.map (cubeLinearEquiv (ι := ι) (G := G))

@[simp]
theorem cubeBasis_apply (c : Configuration ι G) :
    cubeBasis c = cubeDistribution c := by
  simp [cubeBasis, cubeLinearEquiv, cubeTransform]

theorem cubeTransform_surjective :
    Function.Surjective
      (cubeTransform :
        Dist (Configuration ι G) → Dist (Configuration ι G)) := by
  intro u
  refine ⟨subsetSumTransform u, ?_⟩
  have h := LinearMap.congr_fun
    (cubeTransform_comp_subsetSumTransform (ι := ι) (G := G)) u
  simpa using h

end CubeBasis

end GeneralSphereT.PathAlgebra
