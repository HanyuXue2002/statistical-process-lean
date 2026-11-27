import Formalization.CubeBasis

set_option linter.style.header false

/-!
# The nonzero cube basis of the reduced distribution group

This module isolates the reduced consequence of the Boolean cube
basis.  Augmentation takes the cube at the zero configuration to `1` and
every other cube to `0`.  Hence the nonzero cubes form an integral basis of
the augmentation kernel.
-/

noncomputable section

open scoped BigOperators

namespace GeneralSphereT.PathAlgebra

section CubeReduced

variable {ι G : Type*} [LinearOrder ι] [AddCommGroup G]

local instance configurationDecidableEq :
    DecidableEq (Configuration ι G) := Classical.decEq _

/-- Augmentation of a cube is supported only at the zero configuration. -/
theorem augmentation_cubeDistribution (c : Configuration ι G) :
    augmentation (Configuration ι G) (cubeDistribution c) =
      if c = 0 then 1 else 0 := by
  classical
  rw [cubeDistribution_expansion]
  simp only [map_sum, augmentation_single]
  simpa using
    (Finset.sum_powerset_neg_one_pow_card (x := c.support))

/-- A nonzero configuration, used as the index type for reduced cubes. -/
abbrev NonzeroConfiguration (ι G : Type*) [AddCommGroup G] :=
  {c : Configuration ι G // c ≠ 0}

/-- Every cube with nonzero index lies in the augmentation kernel. -/
def reducedCubeDistribution (c : NonzeroConfiguration ι G) :
    RedDist (Configuration ι G) :=
  ⟨cubeDistribution c, by
    change augmentation (Configuration ι G) (cubeDistribution c) = 0
    rw [augmentation_cubeDistribution]
    exact ite_eq_right c.property⟩

@[simp]
theorem reducedCubeDistribution_coe (c : NonzeroConfiguration ι G) :
    (reducedCubeDistribution c : Dist (Configuration ι G)) =
      cubeDistribution c :=
  rfl

/-- The zero coefficient of a subset distribution is always one. -/
theorem subsetDistribution_apply_zero (c : Configuration ι G) :
    subsetDistribution c 0 = 1 := by
  classical
  rw [subsetDistribution]
  rw [Finset.sum_apply']
  rw [Finset.sum_eq_single ∅]
  · simp
  · intro s hs hne
    have hsubset : s ⊆ c.support := Finset.mem_powerset.mp hs
    have htrunc : coordinateTruncation c s ≠ 0 := by
      intro hz
      have hsupp := support_coordinateTruncation c hsubset
      rw [hz, Finsupp.support_zero] at hsupp
      exact hne hsupp.symm
    simp [htrunc]
  · simp

/--
The coefficient of the zero cube is exactly ordinary augmentation.  This is
the coordinate form of the fact that all nonzero cubes are reduced.
-/
theorem subsetSumTransform_apply_zero
    (u : Dist (Configuration ι G)) :
    subsetSumTransform u 0 = augmentation (Configuration ι G) u := by
  classical
  induction u using Finsupp.induction with
  | zero => simp
  | single_add c n u _ _ ih =>
      simp [subsetSumTransform_single, subsetDistribution_apply_zero, ih]

/-- Restrict cube coordinates to nonzero configurations. -/
def restrictNonzero :
    Dist (Configuration ι G) →ₗ[ℤ]
      (NonzeroConfiguration ι G →₀ ℤ) :=
  Finsupp.lsubtypeDomain {c : Configuration ι G | c ≠ 0}

omit [LinearOrder ι] in
@[simp]
theorem restrictNonzero_apply
    (u : Dist (Configuration ι G)) (c : NonzeroConfiguration ι G) :
    restrictNonzero u c = u c :=
  rfl

/-- Extend nonzero-indexed coefficients by zero, without choosing decidable equality. -/
def extendNonzero :
    (NonzeroConfiguration ι G →₀ ℤ) →ₗ[ℤ]
      Dist (Configuration ι G) :=
  Finsupp.lmapDomain ℤ ℤ Subtype.val

omit [LinearOrder ι] in
@[simp]
theorem extendNonzero_single
    (c : NonzeroConfiguration ι G) (n : ℤ) :
    extendNonzero (Finsupp.single c n) = Finsupp.single c.1 n := by
  simp [extendNonzero]

omit [LinearOrder ι] in
/-- Extension followed by restriction is the identity. -/
theorem restrictNonzero_extendNonzero
    (u : NonzeroConfiguration ι G →₀ ℤ) :
    restrictNonzero (extendNonzero u) = u := by
  ext c
  change Finsupp.mapDomain Subtype.val u c.1 = u c
  exact Finsupp.mapDomain_apply Subtype.val_injective u c

omit [LinearOrder ι] in
/-- Restriction is lossless when the omitted zero coefficient vanishes. -/
theorem extendNonzero_restrictNonzero
    (u : Dist (Configuration ι G)) (hzero : u 0 = 0) :
    extendNonzero (restrictNonzero u) = u := by
  ext c
  by_cases hc : c = 0
  · subst c
    have hnotrange :
        (0 : Configuration ι G) ∉
          Set.range (Subtype.val : NonzeroConfiguration ι G → Configuration ι G) := by
      rintro ⟨c, hc⟩
      exact c.2 hc
    rw [show extendNonzero (restrictNonzero u) 0 = 0 by
      exact Finsupp.mapDomain_of_notMem_range _ _ hnotrange]
    exact hzero.symm
  · let c' : NonzeroConfiguration ι G := ⟨c, hc⟩
    change Finsupp.mapDomain Subtype.val (restrictNonzero u) c = u c
    simpa [c'] using
      (Finsupp.mapDomain_apply Subtype.val_injective (restrictNonzero u) c')

/-- Linear synthesis from coefficients indexed by nonzero configurations. -/
def nonzeroCubeSynthesis :
    (NonzeroConfiguration ι G →₀ ℤ) →ₗ[ℤ]
      RedDist (Configuration ι G) :=
  Finsupp.linearCombination ℤ reducedCubeDistribution

@[simp]
theorem nonzeroCubeSynthesis_single
    (c : NonzeroConfiguration ι G) (n : ℤ) :
    nonzeroCubeSynthesis (Finsupp.single c n) =
      n • reducedCubeDistribution c := by
  simp [nonzeroCubeSynthesis]

/-- After forgetting the kernel proof, synthesis is the ordinary cube transform. -/
theorem nonzeroCubeSynthesis_coe
    (u : NonzeroConfiguration ι G →₀ ℤ) :
    (nonzeroCubeSynthesis u : Dist (Configuration ι G)) =
      cubeTransform (extendNonzero u) := by
  classical
  induction u using Finsupp.induction with
  | zero => simp
  | single_add c n u _ _ ih =>
      simp [ih]

/-- Uniqueness of expansion in nonzero cubes. -/
theorem nonzeroCubeSynthesis_injective :
    Function.Injective
      (nonzeroCubeSynthesis (ι := ι) (G := G)) := by
  classical
  intro u v huv
  have hcoe :
      (nonzeroCubeSynthesis u : Dist (Configuration ι G)) =
        (nonzeroCubeSynthesis v : Dist (Configuration ι G)) := by
    exact congrArg Subtype.val huv
  have htransform :
      cubeTransform (extendNonzero u) = cubeTransform (extendNonzero v) := by
    simpa only [nonzeroCubeSynthesis_coe] using hcoe
  have hext : extendNonzero u = extendNonzero v :=
    (cubeLinearEquiv (ι := ι) (G := G)).injective htransform
  have hrestrict := congrArg restrictNonzero hext
  simpa only [restrictNonzero_extendNonzero] using hrestrict

/-- Every reduced distribution has an expansion in nonzero cubes. -/
theorem nonzeroCubeSynthesis_surjective :
    Function.Surjective
      (nonzeroCubeSynthesis (ι := ι) (G := G)) := by
  classical
  intro u
  let coordinates : Dist (Configuration ι G) :=
    subsetSumTransform u.1
  have hzero : coordinates 0 = 0 := by
    rw [show coordinates 0 = subsetSumTransform u.1 0 by rfl,
      subsetSumTransform_apply_zero]
    exact u.2
  let reducedCoordinates : NonzeroConfiguration ι G →₀ ℤ :=
    restrictNonzero coordinates
  refine ⟨reducedCoordinates, Subtype.ext ?_⟩
  rw [nonzeroCubeSynthesis_coe]
  have hext : extendNonzero reducedCoordinates = coordinates := by
    exact extendNonzero_restrictNonzero coordinates hzero
  rw [hext]
  exact LinearMap.congr_fun
    (cubeTransform_comp_subsetSumTransform (ι := ι) (G := G)) u.1

/-- Nonzero-cube coefficients are linearly equivalent to reduced distributions. -/
def nonzeroCubeLinearEquiv :
    (NonzeroConfiguration ι G →₀ ℤ) ≃ₗ[ℤ]
      RedDist (Configuration ι G) :=
  LinearEquiv.ofBijective
    (nonzeroCubeSynthesis (ι := ι) (G := G))
    ⟨nonzeroCubeSynthesis_injective, nonzeroCubeSynthesis_surjective⟩

/-- The cubes indexed by nonzero configurations form an integral basis. -/
def reducedCubeBasis :
    Module.Basis (NonzeroConfiguration ι G) ℤ
      (RedDist (Configuration ι G)) :=
  Finsupp.basisSingleOne.map
    (nonzeroCubeLinearEquiv (ι := ι) (G := G))

@[simp]
theorem reducedCubeBasis_apply (c : NonzeroConfiguration ι G) :
    reducedCubeBasis c = reducedCubeDistribution c := by
  change nonzeroCubeLinearEquiv (Finsupp.single c 1) =
    reducedCubeDistribution c
  change nonzeroCubeSynthesis (Finsupp.single c 1) =
    reducedCubeDistribution c
  simp

end CubeReduced

end GeneralSphereT.PathAlgebra
