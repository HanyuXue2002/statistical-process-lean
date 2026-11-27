import Formalization.CubeKernel
import Formalization.DistributionDifferences
import Formalization.CoordinateExtension

set_option linter.style.header false

/-!
# Anchored coordinates and simplex-restriction locality

This file proves the algebraic content of Theorem 1.2 of the open-disk report.
The configurations are finitely supported functions.  For a finite coordinate
type these are exactly the cochains in the report.  The coefficient group is
an arbitrary additive commutative group, hence includes `AddCircle (1 : ℝ)`.
The coordinate of a configuration `c` is the anchored table on `c.support`
evaluated on its nonzero entries; the empty configuration retains the constant
phase.  No quotient by constant phases is taken.
-/

noncomputable section

open scoped BigOperators
open GeneralSphereT.PathAlgebra

namespace OpenDisk

section Anchored

variable {ι G A : Type*} [LinearOrder ι] [AddCommGroup G] [AddCommGroup A]

/-- Pair an arbitrary phase function with an integral distribution. -/
def phasePairing (f : Configuration ι G → A) : GeneralSphereT.PathAlgebra.Dist (Configuration ι G) →ₗ[ℤ] A :=
  Finsupp.linearCombination ℤ f

@[simp] theorem phasePairing_single (f : Configuration ι G → A)
    (c : Configuration ι G) (n : ℤ) :
    phasePairing f (Finsupp.single c n) = n • f c := by
  simp [phasePairing]

/-- The unique nonredundant anchored coordinates, including the constant term. -/
def anchoredCoordinate (f : Configuration ι G → A) (c : Configuration ι G) : A :=
  phasePairing f (cubeDistribution c)

/-- Recover a function by adding the coordinates of all restrictions. -/
def reconstructPhase (a : Configuration ι G → A) (c : Configuration ι G) : A :=
  ∑ s ∈ c.support.powerset, a (coordinateTruncation c s)

theorem anchoredCoordinate_formula (f : Configuration ι G → A)
    (c : Configuration ι G) :
    anchoredCoordinate f c = ∑ t ∈ c.support.powerset,
      ((-1 : ℤ) ^ t.card) • f (coordinateTruncation c (c.support \ t)) := by
  simp [anchoredCoordinate, cubeDistribution_expansion]

theorem reconstruct_anchoredCoordinate (f : Configuration ι G → A) :
    reconstructPhase (anchoredCoordinate f) = f := by
  funext c
  have h := congrArg (phasePairing f) (cubeDistribution_mobius_inversion c)
  simpa [reconstructPhase, anchoredCoordinate] using h.symm

theorem phasePairing_anchoredCoordinate (f : Configuration ι G → A) :
    phasePairing (anchoredCoordinate f) = (phasePairing f).comp cubeTransform := by
  ext c
  simp [anchoredCoordinate]

theorem phasePairing_reconstructPhase (a : Configuration ι G → A) :
    phasePairing (reconstructPhase a) = (phasePairing a).comp subsetSumTransform := by
  ext c
  simp [reconstructPhase, subsetDistribution]

theorem anchoredCoordinate_reconstruct (a : Configuration ι G → A) :
    anchoredCoordinate (reconstructPhase a) = a := by
  funext c
  rw [anchoredCoordinate, phasePairing_reconstructPhase, LinearMap.comp_apply,
    subsetSumTransform_cubeDistribution]
  simp

/-- Boolean Möbius inversion is an equivalence on all phase tables. -/
def anchoredEquiv : (Configuration ι G → A) ≃ (Configuration ι G → A) where
  toFun := anchoredCoordinate
  invFun := reconstructPhase
  left_inv := reconstruct_anchoredCoordinate
  right_inv := anchoredCoordinate_reconstruct

/-- Existence and uniqueness, with one coordinate for each fully nonzero input. -/
theorem existsUnique_anchored_decomposition (f : Configuration ι G → A) :
    ∃! a : Configuration ι G → A, reconstructPhase a = f := by
  refine ⟨anchoredCoordinate f, reconstruct_anchoredCoordinate f, ?_⟩
  intro a ha
  rw [← ha, anchoredCoordinate_reconstruct]

/-- Anchored table on an arbitrary coordinate set; zero entries are allowed. -/
def anchoredTable (f : Configuration ι G → A) (s : Finset ι)
    (c : Configuration ι G) : A :=
  phasePairing f (cubeOn c s).coeff

theorem anchoredTable_formula (f : Configuration ι G → A)
    (s : Finset ι) (c : Configuration ι G) :
    anchoredTable f s c = ∑ t ∈ s.powerset,
      ((-1 : ℤ) ^ t.card) • f (coordinateTruncation c (s \ t)) := by
  rw [anchoredTable, cubeOn_expansion]
  simp only [AddMonoidAlgebra.coeff_sum, map_sum]
  apply Finset.sum_congr rfl
  intro t ht
  rw [neg_one_pow_mul_delta]
  exact phasePairing_single f _ _

/-- The formula with the same subset and cardinality convention as equation (1.5). -/
theorem anchoredTable_formula_paper (f : Configuration ι G → A)
    (s : Finset ι) (c : Configuration ι G) :
    anchoredTable f s c = ∑ b ∈ s.powerset,
      ((-1 : ℤ) ^ (s.card - b.card)) • f (coordinateTruncation c b) := by
  classical
  rw [anchoredTable_formula]
  refine Finset.sum_bij (fun t _ => s \ t) (fun t _ => Finset.mem_powerset.mpr Finset.sdiff_subset)
    ?_ ?_ ?_
  · intro t ht u hu htu
    have hh := congrArg (fun v => s \ v) htu
    simpa [Finset.sdiff_sdiff_eq_self (Finset.mem_powerset.mp ht),
      Finset.sdiff_sdiff_eq_self (Finset.mem_powerset.mp hu)] using hh
  · intro b hb
    exact ⟨s \ b, Finset.mem_powerset.mpr Finset.sdiff_subset,
      Finset.sdiff_sdiff_eq_self (Finset.mem_powerset.mp hb)⟩
  · intro t ht
    rw [Finset.card_sdiff_of_subset (Finset.mem_powerset.mp ht),
      Nat.sub_sub_self (Finset.card_le_card (Finset.mem_powerset.mp ht))]

theorem anchoredTable_eq_coordinate (f : Configuration ι G → A)
    (s : Finset ι) (c : Configuration ι G) (hs : s ⊆ c.support) :
    anchoredTable f s c = anchoredCoordinate f (coordinateTruncation c s) := by
  rw [anchoredTable, anchoredCoordinate, cubeDistribution, cube_coordinateTruncation c hs]

/-- The table vanishes whenever one of its specified coordinates is zero. -/
theorem anchoredTable_zero_coordinate (f : Configuration ι G → A)
    (s : Finset ι) (c : Configuration ι G) {i : ι}
    (hi : i ∈ s) (hc : c i = 0) : anchoredTable f s c = 0 := by
  have hzero : cubeOn c s = 0 := by
    apply Finset.prod_eq_zero hi
    simp [hc]
  simp [anchoredTable, hzero]

/-- An anchored term depends only on the coordinates named by its set. -/
theorem anchoredTable_congr (f : Configuration ι G → A)
    (s : Finset ι) (c d : Configuration ι G)
    (h : ∀ i ∈ s, c i = d i) : anchoredTable f s c = anchoredTable f s d := by
  unfold anchoredTable cubeOn
  congr 2
  exact Finset.prod_congr rfl (fun i hi => by rw [h i hi])

/-- The literal decomposition over all subsets of a finite coordinate type. -/
theorem sum_anchoredTable [Fintype ι] (f : Configuration ι G → A)
    (c : Configuration ι G) :
    (∑ s ∈ (Finset.univ : Finset ι).powerset, anchoredTable f s c) = f c := by
  have h := congrArg (fun u : ConfigurationRing ι G => phasePairing f u.coeff)
    (cubeOn_mobius_inversion c Finset.univ)
  have htrunc : coordinateTruncation c Finset.univ = c := by
    ext i
    simp
  simpa [anchoredTable, AddMonoidAlgebra.coeff_sum, htrunc, delta] using h

end Anchored

section Locality

variable {ι G A Facet : Type*} [LinearOrder ι] [AddCommGroup G] [AddCommGroup A]

/-- The forward difference of a phase function, with the report's sign convention. -/
def phaseDifference (s : Configuration ι G) (f : Configuration ι G → A)
    (c : Configuration ι G) : A := f (c + s) - f c

/-- Repeated differences in the displayed nesting order of the report. -/
def iteratedPhaseDifference : List (Configuration ι G) →
    (Configuration ι G → A) → Configuration ι G → A
  | [], f => f
  | s :: steps, f => iteratedPhaseDifference steps (phaseDifference s f)

theorem phasePairing_phaseDifference (s : Configuration ι G)
    (f : Configuration ι G → A) :
    phasePairing (phaseDifference s f) =
      (phasePairing f).comp (distributionDifference s) := by
  ext c
  simp [phaseDifference]

/-- Finite differences of functions are exactly dual to differences of distributions. -/
theorem iteratedPhaseDifference_eq_pairing (steps : List (Configuration ι G))
    (f : Configuration ι G → A) (c : Configuration ι G) :
    iteratedPhaseDifference steps f c =
      phasePairing f (iteratedDistributionDifference steps (Finsupp.single c 1)) := by
  induction steps generalizing f with
  | nil => simp [iteratedPhaseDifference]
  | cons s steps ih =>
      rw [iteratedPhaseDifference, ih, phasePairing_phaseDifference]
      rfl

/-- Nonface anchored coordinates vanish. Facets may be any family of coordinate sets. -/
def AnchoredLocal (facets : Facet → Set ι) (f : Configuration ι G → A) : Prop :=
  ∀ c, (∀ ρ, ¬∀ i ∈ c.support, i ∈ facets ρ) → anchoredCoordinate f c = 0

/-- The locality axiom, allowing repeated carriers and arbitrary elementary increments.
For a nonempty facet family, the no-common-facet premise forces a nonempty list. -/
def DifferenceLocal (facets : Facet → Set ι) (f : Configuration ι G → A) : Prop :=
  ∀ steps : List (ι × G),
    (∀ p ∈ steps, p.2 ≠ 0) →
    (∀ ρ, ∃ p ∈ steps, p.1 ∉ facets ρ) →
    ∀ c, iteratedPhaseDifference (steps.map (fun p => Finsupp.single p.1 p.2)) f c = 0

/-- On a nonempty facet family this is exactly the axiom restricted to lists of length at least one. -/
theorem differenceLocal_iff_nonempty_lists [Nonempty Facet]
    (facets : Facet → Set ι) (f : Configuration ι G → A) :
    DifferenceLocal facets f ↔
      ∀ steps : List (ι × G), steps ≠ [] →
        (∀ p ∈ steps, p.2 ≠ 0) →
        (∀ ρ, ∃ p ∈ steps, p.1 ∉ facets ρ) →
        ∀ c, iteratedPhaseDifference (steps.map (fun p => Finsupp.single p.1 p.2)) f c = 0 := by
  constructor
  · intro h steps _hne hp hfac
    exact h steps hp hfac
  · intro h steps hp hfac
    apply h steps _ hp hfac
    intro heq
    obtain ⟨ρ⟩ := ‹Nonempty Facet›
    simpa [heq] using hfac ρ

/-- Kernel-annihilation formulation of anchored locality. -/
theorem anchoredLocal_iff_annihilates_commonKernel
    (facets : Facet → Set ι) (f : Configuration ι G → A) :
    AnchoredLocal facets f ↔
      coordinateCommonRestrictionKernel (G := G) facets ≤ LinearMap.ker (phasePairing f) := by
  rw [coordinateCommonRestrictionKernel_eq_noFacetCubeSpan, noFacetCubeSpan,
    Submodule.span_le]
  constructor
  · intro h u hu
    rcases hu with ⟨c, hc, rfl⟩
    simpa [cubeBasis_apply, anchoredCoordinate] using h c hc
  · intro h c hc
    exact h ⟨c, hc, cubeBasis_apply c⟩

private theorem distributionDifference_zero' :
    distributionDifference (0 : Configuration ι G) = 0 := by
  ext c
  simp

private theorem iteratedDistributionDifference_zero_mem
    (steps : List (Configuration ι G)) (h : (0 : Configuration ι G) ∈ steps)
    (u : GeneralSphereT.PathAlgebra.Dist (Configuration ι G)) : iteratedDistributionDifference steps u = 0 := by
  induction steps with
  | nil => simp at h
  | cons s steps ih =>
      rcases List.mem_cons.mp h with hs | hs
      · subst s
        simp [distributionDifference_zero']
      · simp [ih hs]

/-- A mixed elementary difference with no common facet vanishes under every restriction. -/
theorem elementaryDifference_mem_commonKernel (facets : Facet → Set ι)
    (steps : List (ι × G)) (hsteps : ∀ ρ, ∃ p ∈ steps, p.1 ∉ facets ρ)
    (u : GeneralSphereT.PathAlgebra.Dist (Configuration ι G)) :
    iteratedDistributionDifference (steps.map (fun p => Finsupp.single p.1 p.2)) u ∈
      coordinateCommonRestrictionKernel (G := G) facets := by
  rw [coordinateCommonRestrictionKernel, Submodule.mem_iInf]
  intro ρ
  rw [LinearMap.mem_ker, mapDist_iteratedDistributionDifference_apply]
  apply iteratedDistributionDifference_zero_mem
  obtain ⟨p, hp, hpρ⟩ := hsteps ρ
  apply List.mem_map.mpr
  refine ⟨Finsupp.single p.1 p.2, List.mem_map.mpr ⟨p, hp, rfl⟩, ?_⟩
  exact coordinateRestriction_single_not_mem (facets ρ) hpρ p.2

/-- The full locality axiom follows from vanishing of nonface anchored coordinates. -/
theorem AnchoredLocal.differenceLocal {facets : Facet → Set ι}
    {f : Configuration ι G → A} (h : AnchoredLocal facets f) : DifferenceLocal facets f := by
  intro steps _hne hsteps c
  rw [iteratedPhaseDifference_eq_pairing]
  exact (anchoredLocal_iff_annihilates_commonKernel facets f).mp h
    (elementaryDifference_mem_commonKernel facets steps hsteps _)

/-- Conversely, apply the locality axiom to the active coordinates at the zero cochain. -/
theorem DifferenceLocal.anchoredLocal {facets : Facet → Set ι}
    {f : Configuration ι G → A} (h : DifferenceLocal facets f) : AnchoredLocal facets f := by
  intro c hc
  let steps : List (ι × G) := c.support.toList.map (fun i => (i, c i))
  have hne : ∀ p ∈ steps, p.2 ≠ 0 := by
    intro p hp
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hp
    exact Finsupp.mem_support_iff.mp (Finset.mem_toList.mp hi)
  have hnocommon : ∀ ρ, ∃ p ∈ steps, p.1 ∉ facets ρ := by
    intro ρ
    obtain ⟨i, hi⟩ := not_forall.mp (hc ρ)
    have hi' : i ∈ c.support ∧ i ∉ facets ρ := by
      simpa only [not_imp] using hi
    exact ⟨(i, c i), List.mem_map.mpr ⟨i, Finset.mem_toList.mpr hi'.1, rfl⟩, hi'.2⟩
  have hh := h steps hne hnocommon 0
  rw [iteratedPhaseDifference_eq_pairing] at hh
  simpa [steps, anchoredCoordinate, cubeDistribution_eq_iteratedDistributionDifference,
    activeCoordinateIncrements, List.map_map, Function.comp_def] using hh

/-- The locality equivalence in Theorem 1.2, with the constant anchored coordinate retained. -/
theorem differenceLocal_iff_anchoredLocal (facets : Facet → Set ι)
    (f : Configuration ι G → A) : DifferenceLocal facets f ↔ AnchoredLocal facets f :=
  ⟨DifferenceLocal.anchoredLocal, AnchoredLocal.differenceLocal⟩

end Locality

section FacetSums

variable {ι G A Facet : Type*} [LinearOrder ι] [AddCommGroup G] [AddCommGroup A]

theorem phasePairing_restriction (S : Set ι) (g : Configuration S G → A) :
    phasePairing (fun c => g (coordinateRestriction S c)) =
      (phasePairing g).comp (mapDist (coordinateRestriction S)) := by
  ext c
  simp

/-- A function of one facet has no anchored coordinates outside that facet. -/
theorem anchoredCoordinate_restriction_zero (S : Set ι) (g : Configuration S G → A)
    (c : Configuration ι G) (hc : ¬∀ i ∈ c.support, i ∈ S) :
    anchoredCoordinate (fun d => g (coordinateRestriction S d)) c = 0 := by
  rw [anchoredCoordinate, phasePairing_restriction, LinearMap.comp_apply,
    mapDist_cubeDistribution_eq_zero_of_not_subset S c hc, map_zero]

/-- Vanishing of all invisible anchored terms forces dependence on the restricted input. -/
theorem factors_restriction_of_anchored_zero (S : Set ι) (f : Configuration ι G → A)
    (h : ∀ c, (¬∀ i ∈ c.support, i ∈ S) → anchoredCoordinate f c = 0) :
    ∃ g : Configuration S G → A, ∀ c, f c = g (coordinateRestriction S c) := by
  have hk : LinearMap.ker (mapDist (coordinateRestriction (G := G) S)) ≤
      LinearMap.ker (phasePairing f) := by
    rw [ker_mapDist_coordinateRestriction_eq_cubeSpan, restrictionInvisibleCubeSpan,
      Submodule.span_le]
    rintro u ⟨c, hc, rfl⟩
    simpa [cubeBasis_apply, anchoredCoordinate] using h c hc
  refine ⟨fun d => f (coordinateExtension S d), fun c => ?_⟩
  have hz : phasePairing f
      (Finsupp.single c 1 - Finsupp.single (coordinateExtension S (coordinateRestriction S c)) 1) = 0 :=
    hk (by simp [LinearMap.mem_ker])
  simpa only [map_sub, phasePairing_single, one_smul, sub_eq_zero] using hz

variable [Fintype Facet]

/-- A literal sum of arbitrary functions on the chosen facets. -/
def FacetSum (facets : Facet → Set ι) (f : Configuration ι G → A) : Prop :=
  ∃ g : ∀ ρ, Configuration (facets ρ) G → A,
    ∀ c, f c = ∑ ρ, g ρ (coordinateRestriction (facets ρ) c)

private def assignedAnchored (facets : Facet → Set ι)
    (a : Configuration ι G → A) (ρ : Facet) (c : Configuration ι G) : A := by
  classical
  exact if h : ∃ σ, ∀ i ∈ c.support, i ∈ facets σ then
    if h.choose = ρ then a c else 0
  else 0

private theorem sum_assignedAnchored (facets : Facet → Set ι)
    (f : Configuration ι G → A) (hlocal : AnchoredLocal facets f)
    (c : Configuration ι G) :
    (∑ ρ, assignedAnchored facets (anchoredCoordinate f) ρ c) = anchoredCoordinate f c := by
  classical
  by_cases h : ∃ σ, ∀ i ∈ c.support, i ∈ facets σ
  · simp only [assignedAnchored, dif_pos h]
    simp
  · have hz : anchoredCoordinate f c = 0 := hlocal c (not_exists.mp h)
    simp only [assignedAnchored, dif_neg h, Finset.sum_const_zero, hz]

private theorem assignedAnchored_zero (facets : Facet → Set ι)
    (a : Configuration ι G → A) (ρ : Facet) (c : Configuration ι G)
    (hc : ¬∀ i ∈ c.support, i ∈ facets ρ) :
    assignedAnchored facets a ρ c = 0 := by
  classical
  unfold assignedAnchored
  split_ifs with h hh
  · exact (hc (hh ▸ h.choose_spec)).elim
  · rfl
  · rfl

/-- Assign each allowed anchored coordinate to one containing facet and sum there. -/
theorem AnchoredLocal.facetSum (facets : Facet → Set ι)
    (f : Configuration ι G → A) (hlocal : AnchoredLocal facets f) : FacetSum facets f := by
  classical
  let a := fun ρ => assignedAnchored facets (anchoredCoordinate f) ρ
  have hfactor : ∀ ρ, ∃ g : Configuration (facets ρ) G → A,
      ∀ c, reconstructPhase (a ρ) c = g (coordinateRestriction (facets ρ) c) := by
    intro ρ
    apply factors_restriction_of_anchored_zero
    intro c hc
    rw [anchoredCoordinate_reconstruct]
    exact assignedAnchored_zero facets _ ρ c hc
  choose g hg using hfactor
  refine ⟨g, fun c => ?_⟩
  calc
    f c = reconstructPhase (anchoredCoordinate f) c :=
      congrFun (reconstruct_anchoredCoordinate f).symm c
    _ = ∑ s ∈ c.support.powerset, ∑ ρ, a ρ (coordinateTruncation c s) := by
      apply Finset.sum_congr rfl
      intro s hs
      exact (sum_assignedAnchored facets f hlocal _).symm
    _ = ∑ ρ, reconstructPhase (a ρ) c := by
      exact Finset.sum_comm
    _ = ∑ ρ, g ρ (coordinateRestriction (facets ρ) c) := by
      apply Finset.sum_congr rfl
      intro ρ hρ
      exact hg ρ c

theorem phasePairing_sum (fs : Facet → Configuration ι G → A) :
    phasePairing (fun c => ∑ ρ, fs ρ c) = ∑ ρ, phasePairing (fs ρ) := by
  ext c
  simp

/-- Every sum of facet-restriction functions has the required nonface vanishing. -/
theorem FacetSum.anchoredLocal {facets : Facet → Set ι}
    {f : Configuration ι G → A} (h : FacetSum facets f) : AnchoredLocal facets f := by
  obtain ⟨g, hg⟩ := h
  have hf : f = fun c => ∑ ρ, g ρ (coordinateRestriction (facets ρ) c) := funext hg
  intro c hc
  rw [hf, anchoredCoordinate, phasePairing_sum, LinearMap.sum_apply]
  apply Finset.sum_eq_zero
  intro ρ hρ
  exact anchoredCoordinate_restriction_zero (facets ρ) (g ρ) c (hc ρ)

/-- The local-sum equivalence of Theorem 1.2 for any finite facet family. -/
theorem differenceLocal_iff_facetSum (facets : Facet → Set ι)
    (f : Configuration ι G → A) : DifferenceLocal facets f ↔ FacetSum facets f := by
  rw [differenceLocal_iff_anchoredLocal]
  exact ⟨AnchoredLocal.facetSum facets f, FacetSum.anchoredLocal⟩

end FacetSums

end OpenDisk
