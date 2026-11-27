import Formalization.OpenDisk.PhaseDuality
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Topology.Algebra.Group.Basic

set_option linter.style.header false

/-!
# Pointwise topology on phase characters

All character groups carry the topology of pointwise convergence into the
actual real circle.  They are compact Hausdorff groups, and the restriction
duality of Proposition 2.1 is a homeomorphism for the quotient topology.
-/

noncomputable section

namespace OpenDisk.PhaseDuality

variable {D E : Type*} [AddCommGroup D] [AddCommGroup E]

/-- Pointwise topology on real-circle characters. -/
instance characterTopologicalSpace : TopologicalSpace (D →ₗ[ℤ] Phase) :=
  TopologicalSpace.induced (fun χ : D →ₗ[ℤ] Phase => (χ : D → Phase)) inferInstance

theorem character_isEmbedding :
    Topology.IsEmbedding (fun χ : D →ₗ[ℤ] Phase => (χ : D → Phase)) :=
  ⟨⟨rfl⟩, DFunLike.coe_injective⟩

instance characterT2Space : T2Space (D →ₗ[ℤ] Phase) :=
  character_isEmbedding.t2Space

instance characterTopologicalAddGroup : IsTopologicalAddGroup (D →ₗ[ℤ] Phase) := by
  let h : (D →ₗ[ℤ] Phase) →+ (D → Phase) :=
    { toFun := fun χ => χ
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  exact Topology.IsInducing.topologicalAddGroup h character_isEmbedding.isInducing

theorem continuous_character_evaluation (x : D) :
    Continuous (fun χ : D →ₗ[ℤ] Phase => χ x) :=
  (continuous_apply x).comp character_isEmbedding.continuous

theorem character_range :
    Set.range (fun χ : D →ₗ[ℤ] Phase => (χ : D → Phase)) =
      {f : D → Phase | ∀ x y, f (x + y) = f x + f y} := by
  ext f
  constructor
  · rintro ⟨χ, rfl⟩
    exact χ.map_add
  · intro hf
    let χ : D →+ Phase :=
      { toFun := f
        map_zero' := by
          have h : f 0 + f 0 = f 0 := by simpa using (hf 0 0).symm
          exact add_eq_left.mp h
        map_add' := hf }
    exact ⟨χ.toIntLinearMap, rfl⟩

theorem character_isClosedEmbedding :
    Topology.IsClosedEmbedding (fun χ : D →ₗ[ℤ] Phase => (χ : D → Phase)) := by
  refine ⟨character_isEmbedding, ?_⟩
  rw [character_range]
  exact isClosed_setOfPred_map_add D Phase

instance characterCompactSpace : CompactSpace (D →ₗ[ℤ] Phase) :=
  character_isClosedEmbedding.compactSpace

theorem isClosed_annihilator (N : Submodule ℤ D) :
    IsClosed (annihilator N : Set (D →ₗ[ℤ] Phase)) := by
  change IsClosed {χ : D →ₗ[ℤ] Phase | ∀ x, ∀ _hx : x ∈ N, χ x = 0}
  simp only [Set.ofPred_forall]
  exact isClosed_iInter fun x => isClosed_iInter fun _hx =>
    isClosed_eq (continuous_character_evaluation x) continuous_const

instance annihilatorCompactSpace (N : Submodule ℤ D) : CompactSpace (annihilator N) :=
  isCompact_iff_compactSpace.mp (isClosed_annihilator N).isCompact

section Tables

variable {X : Type*}

theorem continuous_evaluate_distribution (u : Distribution X) :
    Continuous (fun φ : X → Phase => evaluate φ u) := by
  induction u using Finsupp.induction with
  | zero => simpa using (continuous_const : Continuous (fun _ : X → Phase => (0 : Phase)))
  | single_add x n u _ _ ih =>
    have hs : Continuous (fun t : Phase => n • t) := continuous_zsmul n
    have h : Continuous (fun φ : X → Phase => n • φ x + evaluate φ u) :=
      Continuous.add (hs.comp (continuous_apply x)) ih
    convert h using 1
    funext φ
    simp only [map_add, evaluate_single]

theorem continuous_phaseTableEquiv :
    Continuous (phaseTableEquiv (X := X)) := by
  apply continuous_induced_rng.mpr
  exact continuous_pi continuous_evaluate_distribution

theorem continuous_phaseTableEquiv_symm :
    Continuous (phaseTableEquiv (X := X)).symm :=
  continuous_pi fun x => continuous_character_evaluation (Finsupp.single x 1)

/-- Full phase tables have exactly the pointwise character topology. -/
def phaseTableHomeomorph : (X → Phase) ≃ₜ (Distribution X →ₗ[ℤ] Phase) where
  toEquiv := phaseTableEquiv.toEquiv
  continuous_toFun := continuous_phaseTableEquiv
  continuous_invFun := continuous_phaseTableEquiv_symm

variable (d : D →+ E) (hd : Function.Surjective d)

theorem continuous_closedPhaseTableEquiv : Continuous (closedPhaseTableEquiv d hd) :=
  continuous_pi fun b => (continuous_apply (Function.surjInv hd b)).comp continuous_subtype_val

theorem continuous_closedPhaseTableEquiv_symm :
    Continuous (closedPhaseTableEquiv d hd).symm := by
  apply Continuous.subtype_mk
  exact continuous_pi fun c => continuous_apply (d c)

def closedPhaseTableHomeomorph : closedInvariant d ≃ₜ (E → Phase) where
  toEquiv := (closedPhaseTableEquiv d hd).toEquiv
  continuous_toFun := continuous_closedPhaseTableEquiv d hd
  continuous_invFun := continuous_closedPhaseTableEquiv_symm d hd

def closedPhaseCharacterHomeomorph :
    closedInvariant d ≃ₜ (Distribution E →ₗ[ℤ] Phase) :=
  (closedPhaseTableHomeomorph d hd).trans phaseTableHomeomorph

end Tables

theorem continuous_restrictCharacter (J N : Submodule ℤ D) :
    Continuous (restrictCharacter J N) := by
  apply continuous_induced_rng.mpr
  apply continuous_pi
  intro x
  refine Submodule.Quotient.induction_on _ x ?_
  intro y
  exact (continuous_character_evaluation y.1).comp continuous_subtype_val

/-- Topological form of the general integral-annihilator duality. -/
def phaseQuotientHomeomorph (J N : Submodule ℤ D) (hJN : J ≤ N) :
    (annihilator J ⧸ localCharacters J N) ≃ₜ
      (IntegralQuotient J N →ₗ[ℤ] Phase) := by
  letI : CompactSpace (annihilator J ⧸ localCharacters J N) :=
    Function.Surjective.compactSpace (localCharacters J N).mkQL.continuous
      (localCharacters J N).mkQ_surjective
  let e := phaseQuotientEquiv J N hJN
  apply Continuous.homeoOfEquivCompactToT2 (f := e.toEquiv)
  apply (localCharacters J N).isQuotientMap_mkQL.continuous_iff.mpr
  convert continuous_restrictCharacter J N using 1
  funext x
  simp [e, phaseQuotientEquiv]

end OpenDisk.PhaseDuality
