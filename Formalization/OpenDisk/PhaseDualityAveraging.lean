import Formalization.OpenDisk.PhaseDualityModelTopology
import Formalization.RelativePrimitiveSection

set_option linter.style.header false

/-!
# Finite closed-shift averaging

Summing a local phase table over the *actual finite group* of globally
closed shifts multiplies a closed-invariant table by the order of that
group.  If local closed shifts extend globally, each averaged local table
factors through local curvature.  The extension condition is proved from
the existing explicit relative primitive sections below.
-/

noncomputable section

open scoped BigOperators
open GeneralSphereT.PathAlgebra

namespace OpenDisk.PhaseDuality

section Extension

variable {ι G B Facet : Type*} [LinearOrder ι] [AddCommGroup G] [AddCommGroup B]
variable (facets : Facet → Set ι) (d : Configuration ι G →+ B)
variable {BAt : Facet → Type*} [∀ ρ, AddCommGroup (BAt ρ)]
variable (L : FacetRestrictionData
  (CAt := fun ρ => Configuration (facets ρ) G) (BAt := BAt) d)

/-- Explicit normalized primitive sections produce genuine global closed
extensions of every local closed configuration. -/
theorem closed_extension_of_relativePrimitiveSections
    (hprimitive : ∀ ρ, L.primitiveRes ρ = coordinateRestriction (facets ρ))
    (S : RelativePrimitiveSectionData facets L)
    (hzero : ∀ ρ (i : facets ρ), S.localPrimitive ρ i 0 = 0)
    (ρ : Facet) (z : Configuration (facets ρ) G) (hz : L.localD ρ z = 0) :
    ∃ w : Configuration ι G, d w = 0 ∧ L.primitiveRes ρ w = z := by
  classical
  by_cases hi : Nonempty (facets ρ)
  · let i : facets ρ := Classical.choice hi
    let c := coordinateExtension (facets ρ) z
    have hc : L.primitiveRes ρ c = z := by
      rw [hprimitive]
      exact coordinateRestriction_coordinateExtension _ _
    have hd : L.physicalRes ρ (d c) = 0 := by
      have h := DFunLike.congr_fun (L.commutes ρ) c
      simpa only [AddMonoidHom.comp_apply, hc, hz] using h
    refine ⟨c - S.globalPrimitive i.1 (d c), ?_, ?_⟩
    · rw [map_sub, S.map_globalPrimitive, sub_self]
    · rw [map_sub, hc, hprimitive,
        S.restrict_globalPrimitive ρ i.1 i.2, hd, hzero, sub_zero]
  · have hz0 : z = 0 := by
      ext i
      exact (hi ⟨i⟩).elim
    exact ⟨0, map_zero _, by simp [hz0]⟩

end Extension

section Averaging

variable {C B P Facet : Type*}
variable [AddCommGroup C] [AddCommGroup B] [AddCommGroup P] [Fintype Facet]
variable {CAt BAt : Facet → Type*}
variable [∀ ρ, AddCommGroup (CAt ρ)] [∀ ρ, AddCommGroup (BAt ρ)]
variable (d : C →+ B) (L : FacetRestrictionData (CAt := CAt) (BAt := BAt) d)
variable [Fintype d.ker]

/-- Finite averaging only uses addition, so it works for arbitrary
abelian-group-valued tables and does not divide circle phases. -/
def averageLocal (g : ∀ ρ, CAt ρ → P) (ρ : Facet) (a : CAt ρ) : P :=
  ∑ z : d.ker, g ρ (a + L.primitiveRes ρ z)

theorem averageLocal_invariant
    (hExt : ∀ ρ (z : CAt ρ), L.localD ρ z = 0 →
      ∃ w : C, d w = 0 ∧ L.primitiveRes ρ w = z)
    (g : ∀ ρ, CAt ρ → P) (ρ : Facet) (z : CAt ρ)
    (hz : L.localD ρ z = 0) (a : CAt ρ) :
    averageLocal d L g ρ (a + z) = averageLocal d L g ρ a := by
  obtain ⟨w, hw, hwr⟩ := hExt ρ z hz
  let w' : d.ker := ⟨w, hw⟩
  have hs := Equiv.sum_comp (Equiv.addLeft w')
    (fun t : d.ker => g ρ (a + L.primitiveRes ρ t))
  change (∑ t : d.ker, g ρ (a + L.primitiveRes ρ (w' + t))) =
    ∑ t : d.ker, g ρ (a + L.primitiveRes ρ t) at hs
  simpa only [averageLocal, w', AddSubgroup.coe_add,
    map_add, AddSubgroup.coe_mk, hwr, add_assoc] using hs

theorem averageLocal_factorsThrough
    (hExt : ∀ ρ (z : CAt ρ), L.localD ρ z = 0 →
      ∃ w : C, d w = 0 ∧ L.primitiveRes ρ w = z)
    (g : ∀ ρ, CAt ρ → P) (ρ : Facet) :
    Function.FactorsThrough (averageLocal d L g ρ) (L.localD ρ) := by
  intro a b hab
  have hz : L.localD ρ (a - b) = 0 := by simp [map_sub, hab]
  have h := averageLocal_invariant d L hExt g ρ (a - b) hz b
  have he : b + (a - b) = a := by abel
  rwa [he] at h

/-- Averaging every local summand proves the finite exponent bound in the
closed-SPT quotient.  Local curvature maps need not be surjective. -/
theorem finite_average_curvature_decomposition
    (hExt : ∀ ρ (z : CAt ρ), L.localD ρ z = 0 →
      ∃ w : C, d w = 0 ∧ L.primitiveRes ρ w = z)
    (f : C → P) (hf : ∀ (z : d.ker) c, f (c + z) = f c)
    (g : ∀ ρ, CAt ρ → P) (hlocal : ∀ c, f c = ∑ ρ, g ρ (L.primitiveRes ρ c)) :
    ∃ k : ∀ ρ, BAt ρ → P, ∀ c,
      Fintype.card d.ker • f c = ∑ ρ, k ρ (L.physicalRes ρ (d c)) := by
  classical
  let k : ∀ ρ, BAt ρ → P := fun ρ =>
    Function.extend (L.localD ρ) (averageLocal d L g ρ) (fun _ => 0)
  have hk (ρ : Facet) (a : CAt ρ) :
      k ρ (L.localD ρ a) = averageLocal d L g ρ a :=
    (averageLocal_factorsThrough d L hExt g ρ).extend_apply (fun _ => 0) a
  refine ⟨k, fun c => ?_⟩
  calc
    Fintype.card d.ker • f c = ∑ z : d.ker, f (c + z) := by simp [hf]
    _ = ∑ z : d.ker, ∑ ρ, g ρ (L.primitiveRes ρ c + L.primitiveRes ρ z) := by
      apply Finset.sum_congr rfl
      intro z _
      rw [hlocal]
      simp only [map_add]
    _ = ∑ ρ, averageLocal d L g ρ (L.primitiveRes ρ c) := Finset.sum_comm
    _ = ∑ ρ, k ρ (L.physicalRes ρ (d c)) := by
      apply Finset.sum_congr rfl
      intro ρ _
      have hc := DFunLike.congr_fun (L.commutes ρ) c
      change L.physicalRes ρ (d c) = L.localD ρ (L.primitiveRes ρ c) at hc
      rw [hc, hk]

end Averaging

section ClosedPhase

variable {ι G B Facet : Type*} [LinearOrder ι] [AddCommGroup G] [AddCommGroup B]
variable [Fintype Facet]
variable (facets : Facet → Set ι) (d : Configuration ι G →+ B)
variable {BAt : Facet → Type*} [∀ ρ, AddCommGroup (BAt ρ)]
variable (L : FacetRestrictionData
  (CAt := fun ρ => Configuration (facets ρ) G) (BAt := BAt) d)
variable [Fintype d.ker]

/-- The order of the actual closed-shift group kills every class in the
original phase-table quotient. -/
theorem closedSPT_card_smul_mem_facetCurvature
    (hprimitive : ∀ ρ, L.primitiveRes ρ = coordinateRestriction (facets ρ))
    (hd : Function.Surjective d)
    (hExt : ∀ ρ (z : Configuration (facets ρ) G), L.localD ρ z = 0 →
      ∃ w : Configuration ι G, d w = 0 ∧ L.primitiveRes ρ w = z)
    (φ : closedSPT facets d hd) :
    Fintype.card d.ker • φ ∈ facetCurvaturePhases facets d L hd := by
  have hφ := (mem_closedSPT_iff facets d hd φ.1).mp φ.2
  obtain ⟨g, hg⟩ := (differenceLocal_iff_facetSum facets φ.1.1).mp hφ
  obtain ⟨k, hk⟩ := finite_average_curvature_decomposition d L hExt φ.1.1
    (fun z c => φ.1.2 z z.2 c) g (fun c => by simpa only [hprimitive] using hg c)
  apply (mem_facetCurvaturePhases_iff facets d L hd _).mpr
  exact ⟨k, hk⟩

end ClosedPhase

end OpenDisk.PhaseDuality
