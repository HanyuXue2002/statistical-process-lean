import Formalization.OpenDisk.Locality

set_option linter.style.header false

/-!
# Literal uniqueness of the anchored family

The core file proves uniqueness in the nonredundant coordinates indexed by
configurations. Here we derive the report's literal formulation: among all
families indexed by coordinate subsets, dependence on that subset and
vanishing at a zero entry make the displayed decomposition unique.
-/

noncomputable section

open scoped BigOperators
open GeneralSphereT.PathAlgebra

namespace OpenDisk

variable {ι G A : Type*} [LinearOrder ι] [Fintype ι] [AddCommGroup G] [AddCommGroup A]

/-- The three properties stated for a candidate family in equation (1.5). -/
def IsAnchoredDecomposition (f : Configuration ι G → A)
    (F : Finset ι → Configuration ι G → A) : Prop :=
  (∀ s c d, (∀ i ∈ s, c i = d i) → F s c = F s d) ∧
  (∀ s c i, i ∈ s → c i = 0 → F s c = 0) ∧
  (∀ c, f c = ∑ s ∈ (Finset.univ : Finset ι).powerset, F s c)

theorem anchoredTable_is_decomposition (f : Configuration ι G → A) :
    IsAnchoredDecomposition f (anchoredTable f) := by
  refine ⟨anchoredTable_congr f, ?_, ?_⟩
  · intro s c i hi hc
    exact anchoredTable_zero_coordinate f s c hi hc
  · intro c
    exact (sum_anchoredTable f c).symm

/-- Every anchored candidate is the explicit Möbius family. -/
theorem anchored_decomposition_unique (f : Configuration ι G → A)
    (F : Finset ι → Configuration ι G → A) (hF : IsAnchoredDecomposition f F) :
    F = anchoredTable f := by
  classical
  obtain ⟨hdep, hzero, hsum⟩ := hF
  let a : Configuration ι G → A := fun c => F c.support c
  have hrec : reconstructPhase a = f := by
    funext c
    calc
      reconstructPhase a c = ∑ s ∈ c.support.powerset, F s c := by
        apply Finset.sum_congr rfl
        intro s hs
        change F (coordinateTruncation c s).support (coordinateTruncation c s) = F s c
        rw [support_coordinateTruncation c (Finset.mem_powerset.mp hs)]
        apply hdep
        intro i hi
        simp [coordinateTruncation_apply, hi]
      _ = ∑ s ∈ (Finset.univ : Finset ι).powerset, F s c := by
        apply Finset.sum_subset
        · intro s hs
          exact Finset.mem_powerset.mpr (Finset.subset_univ s)
        · intro s hs hnot
          have hns : ¬s ⊆ c.support := fun h => hnot (Finset.mem_powerset.mpr h)
          obtain ⟨i, hi, hic⟩ := Finset.not_subset.mp hns
          exact hzero s c i hi (Finsupp.notMem_support_iff.mp hic)
      _ = f c := (hsum c).symm
  have ha : a = anchoredCoordinate f := by
    rw [← hrec, anchoredCoordinate_reconstruct]
  funext s c
  by_cases hs : s ⊆ c.support
  · rw [anchoredTable_eq_coordinate f s c hs, ← ha]
    change F s c = F (coordinateTruncation c s).support (coordinateTruncation c s)
    rw [support_coordinateTruncation c hs]
    apply hdep
    intro i hi
    simp [coordinateTruncation_apply, hi]
  · obtain ⟨i, hi, hic⟩ := Finset.not_subset.mp hs
    have hci := Finsupp.notMem_support_iff.mp hic
    rw [hzero s c i hi hci, anchoredTable_zero_coordinate f s c hi hci]

/-- The complete literal existence-and-uniqueness assertion of Theorem 1.2. -/
theorem existsUnique_anchored_family (f : Configuration ι G → A) :
    ∃! F : Finset ι → Configuration ι G → A, IsAnchoredDecomposition f F := by
  exact ⟨anchoredTable f, anchoredTable_is_decomposition f,
    fun F hF => anchored_decomposition_unique f F hF⟩

/-- Equation (1.6) in its literal subset-indexed formulation. -/
theorem anchoredLocal_iff_anchoredTable {Facet : Type*} (facets : Facet → Set ι)
    (f : Configuration ι G → A) :
    AnchoredLocal facets f ↔
      ∀ s, (∀ ρ, ¬∀ i ∈ s, i ∈ facets ρ) → ∀ c, anchoredTable f s c = 0 := by
  classical
  constructor
  · intro h s hs c
    by_cases hsc : s ⊆ c.support
    · rw [anchoredTable_eq_coordinate f s c hsc]
      apply h
      simpa only [support_coordinateTruncation c hsc] using hs
    · obtain ⟨i, hi, hic⟩ := Finset.not_subset.mp hsc
      exact anchoredTable_zero_coordinate f s c hi (Finsupp.notMem_support_iff.mp hic)
  · intro h c hc
    have hh := h c.support hc c
    rwa [anchoredTable_eq_coordinate f c.support c (Finset.Subset.refl _),
      coordinateTruncation_support] at hh

end OpenDisk
