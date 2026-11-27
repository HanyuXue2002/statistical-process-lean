import Formalization.OpenDisk.JointLocality
import Formalization.OpenDisk.SymmetryAverage

/-!
# Intrinsic restriction locality for symmetry tables

The condition is exactly the finite-difference form (3.12), including its
nonempty list convention. Marked-local matching hoppings imply this condition;
thus the symmetry forgetful map is well-defined without assuming its target
locality. The reverse local-lifting implication is treated separately.
-/

noncomputable section
open GeneralSphereT.PathAlgebra

namespace OpenDisk

variable {ι G B P Facet : Type*} [LinearOrder ι] [AddCommGroup G]
  [AddCommGroup B] [AddCommGroup P]

theorem rawDifference_zero {X : Type*} [AddCommGroup X] :
    distributionDifference (0 : X) = 0 := by
  ext c
  simp

theorem rawIteratedDifference_zero_mem {X : Type*} [AddCommGroup X]
    (steps : List X) (h : (0 : X) ∈ steps) (u : GeneralSphereT.PathAlgebra.Dist X) :
    iteratedDistributionDifference steps u = 0 := by
  induction steps with
  | nil => simp at h
  | cons s steps ih =>
      rcases List.mem_cons.mp h with hs | hs
      · subst s; simp [rawDifference_zero]
      · simp [ih hs]

/-- A local phase vanishes on any mixed difference with one invisible direction
per facet; the directions need not themselves be elementary. -/
theorem AnchoredLocal.arbitrary_differences {facets : Facet → Set ι}
    {f : Configuration ι G → P} (hf : AnchoredLocal facets f)
    (steps : List (Configuration ι G))
    (hsteps : ∀ ρ, ∃ s ∈ steps, coordinateRestriction (facets ρ) s = 0)
    (v : Configuration ι G) : iteratedPhaseDifference steps f v = 0 := by
  rw [iteratedPhaseDifference_eq_pairing]
  apply (anchoredLocal_iff_annihilates_commonKernel facets f).1 hf
  rw [coordinateCommonRestrictionKernel, Submodule.mem_iInf]
  intro ρ
  rw [LinearMap.mem_ker, mapDist_iteratedDistributionDifference_apply]
  apply rawIteratedDifference_zero_mem
  obtain ⟨s, hs, hzero⟩ := hsteps ρ
  exact List.mem_map.mpr ⟨s, hs, hzero⟩

/-- The literal restriction-local symmetry axiom (3.12). -/
def RestrictionSymmetryLocal (facets : Facet → Set ι)
    (d : Configuration ι G →+ B) (F : SymmetryPhase d P) : Prop :=
  ∀ (z : d.ker) (steps : List (ι × G)), steps ≠ [] →
    (∀ p ∈ steps, p.2 ≠ 0) →
    (∀ ρ, coordinateRestriction (facets ρ) (z : Configuration ι G) = 0 ∨
      ∃ p ∈ steps, p.1 ∉ facets ρ) →
    ∀ v, iteratedPhaseDifference (steps.map (fun p => Finsupp.single p.1 p.2))
      (fun v => F z v) v = 0

/-- The forward implication of Theorem 3.8 for literal cochain coordinates. -/
theorem restrictionSymmetryLocal_of_matching (facets : Facet → Set ι)
    (d : Configuration ι G →+ B) (F : SymmetryPhase d P)
    (hlocal : ∀ e : ElementaryLabel ι G, ∃ L : Configuration ι G → P,
      MarkedLocal facets {e.1.1} L ∧
      ∀ (z : d.ker) v, difference L z v = difference (fun v => F z v) (elementaryStep e) v) :
    RestrictionSymmetryLocal facets d F := by
  intro z steps hne hactive hfac v
  cases steps with
  | nil => exact (hne rfl).elim
  | cons p steps =>
      let e : ElementaryLabel ι G := ⟨p, hactive p List.mem_cons_self⟩
      obtain ⟨L, hL, hmatch⟩ := hlocal e
      have hfun : phaseDifference (Finsupp.single p.1 p.2) (fun v => F z v) =
          phaseDifference z L := funext fun v => (hmatch z v).symm
      change iteratedPhaseDifference (steps.map (fun p => Finsupp.single p.1 p.2))
        (phaseDifference (Finsupp.single p.1 p.2) (fun v => F z v)) v = 0
      rw [hfun]
      change iteratedPhaseDifference
        ((z : Configuration ι G) :: steps.map (fun p => Finsupp.single p.1 p.2)) L v = 0
      apply hL.arbitrary_differences
      intro ρ
      rcases hfac ρ.1 with hz | ⟨q, hq, hqρ⟩
      · exact ⟨z, List.mem_cons_self, hz⟩
      · rcases List.mem_cons.mp hq with heq | hq
        · subst q
          exact (hqρ (ρ.2 p.1 (Finset.mem_singleton_self _))).elim
        · exact ⟨Finsupp.single q.1 q.2,
            List.mem_cons_of_mem _ (List.mem_map.mpr ⟨q, hq, rfl⟩),
            coordinateRestriction_single_not_mem (facets ρ.1) hqρ q.2⟩

/-- The first forgetful map really has restriction-local symmetry as its target. -/
theorem joint_forgetSymmetry_local (facets : Facet → Set ι)
    (d : Configuration ι G →+ B) (x : LocalJointPhase facets d P) :
    RestrictionSymmetryLocal facets d (forgetSymmetry d elementaryStep
      (markedFunctionSubgroup facets) x) := by
  apply restrictionSymmetryLocal_of_matching
  intro e
  exact ⟨x.1.2 e, x.2.1 e, x.2.2 e⟩

/-- Every symmetry row is local, as required by the averaging proof in 3.4. -/
theorem RestrictionSymmetryLocal.row_local [Nonempty Facet]
    {facets : Facet → Set ι} {d : Configuration ι G →+ B} {F : SymmetryPhase d P}
    (hF : RestrictionSymmetryLocal facets d F) (z : d.ker) :
    DifferenceLocal facets (fun v => F z v) := by
  rw [differenceLocal_iff_nonempty_lists]
  intro steps hne hactive hfac
  exact hF z steps hne hactive (fun ρ => Or.inr (hfac ρ))

/-- The annihilator bound of Proposition 3.4 with the actual local-function subgroup. -/
theorem restrictionSymmetry_card_bound [Nonempty Facet]
    (facets : Facet → Set ι) (d : Configuration ι G →+ B) [Fintype d.ker]
    (F : SymmetryPhase d P) (hF : RestrictionSymmetryLocal facets d F) :
    Fintype.card d.ker • F ∈ (localFunctionSubgroup (G := G) facets P).map (phaseDerivative d) := by
  apply card_nsmul_mem_localDerivative
  intro z
  exact (differenceLocal_iff_anchoredLocal facets _).1 (hF.row_local z)

end OpenDisk
