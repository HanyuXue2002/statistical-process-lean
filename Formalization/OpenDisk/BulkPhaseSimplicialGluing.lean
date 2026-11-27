import Formalization.OpenDisk.BulkPhaseLocalGluing
import Formalization.SimplicialFacetData

/-!
# Actual simplicial locality of the canonical completion inverse

For a finite complex with a distinguished new vertex, actual facets are
the simplices avoiding that vertex and cap facets are the simplices containing
it. The zero-new-coordinate slice keeps exactly those cochain coordinates
avoiding the new vertex. Deleting that vertex from a cap facet verifies the
boundary incidence condition of the general local gluing theorem.

This is the literal cochain locality bridge; it does not assume that an
arbitrary topological ball comes with an unformalized sphere identification.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 2000000

namespace OpenDisk.BulkPhaseSimplicialGluing

open GeneralSphereT.SimplicialCochain GeneralSphereT.PathAlgebra
open BulkPhaseLocalGluing

variable {V G P : Type*} [LinearOrder V] [Fintype V]
  [AddCommGroup G] [AddCommGroup P]
variable (K : AbstractSimplicialComplex V) (p : V)

abbrev ActualFacet := {σ : NonemptySimplex K // p ∉ σ.val}
abbrev CapFacet := {σ : NonemptySimplex K // p ∈ σ.val}

local instance actualFacetFintype : Fintype (ActualFacet K p) := Fintype.ofFinite _
local instance capFacetFintype : Fintype (CapFacet K p) := Fintype.ofFinite _
local instance allFacetFintype : Fintype (NonemptySimplex K) := Fintype.ofFinite _
local instance simplexOrder (n : ℕ) : LinearOrder (Simplex K n) := by
  classical
  exact linearOrderOfSTO WellOrderingRel

def actualCoordinates (n : ℕ) : Set (Simplex K n) := {τ | p ∉ τ.val}
def actualFacets (n : ℕ) (σ : ActualFacet K p) : Set (Simplex K n) := facesIn K n σ.val
def capFacets (n : ℕ) (σ : CapFacet K p) : Set (Simplex K n) := facesIn K n σ.val

/-- An old vertex provides an actual facet, as in a nonempty actual bulk. -/
theorem actualFacet_nonempty_of_vertex (v : V) (hvp : v ≠ p) : Nonempty (ActualFacet K p) :=
  ⟨⟨⟨{v}, K.singleton_mem v⟩, by simpa using hvp.symm⟩⟩

theorem actualFacet_inside (n : ℕ) (σ : ActualFacet K p) :
    actualFacets K p n σ ⊆ actualCoordinates K p n := by
  intro τ hτ hp
  exact σ.property (hτ hp)

/-- The old part of a cap simplex lies in its face obtained by deleting the
new vertex. The empty deleted face causes no problem in nonnegative degree. -/
theorem cap_boundary_in_actual [Nonempty (ActualFacet K p)] (n : ℕ)
    (σ : CapFacet K p) :
    ∃ ρ : ActualFacet K p,
      capFacets K p n σ ∩ actualCoordinates K p n ⊆ actualFacets K p n ρ := by
  classical
  by_cases hne : (σ.val.val.erase p).Nonempty
  · have hmem : σ.val.val.erase p ∈ K :=
      (K.isRelLowerSet_faces σ.val.property).2 (Finset.erase_subset _ _) hne
    refine ⟨⟨⟨σ.val.val.erase p, hmem⟩, by simp⟩, ?_⟩
    intro τ hτ x hx
    exact Finset.mem_erase.mpr ⟨fun hxp => hτ.2 (hxp ▸ hx), hτ.1 hx⟩
  · refine ⟨Classical.choice inferInstance, ?_⟩
    intro τ hτ
    have hempty : σ.val.val.erase p = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    have hsub : τ.val ⊆ σ.val.val.erase p := by
      intro x hx
      exact Finset.mem_erase.mpr ⟨fun hxp => hτ.2 (hxp ▸ hx), hτ.1 hx⟩
    have htzero : τ.val = ∅ := Finset.subset_empty.mp (hempty ▸ hsub)
    have hcard := τ.property.2
    rw [htzero, Finset.card_empty] at hcard
    omega

/-- Splitting the all-simplex facet family by the new vertex preserves the
literal locality predicate. -/
theorem local_all_iff_split (n : ℕ) (f : Cochain K n G → P) :
    AnchoredLocal (fun σ : NonemptySimplex K => facesIn K n σ) f ↔
      AnchoredLocal (Sum.elim (actualFacets K p n) (capFacets K p n)) f := by
  constructor
  · apply local_refinement
    intro σ
    by_cases hp : p ∈ σ.val
    · exact ⟨Sum.inr ⟨σ, hp⟩, Set.Subset.rfl⟩
    · exact ⟨Sum.inl ⟨σ, hp⟩, Set.Subset.rfl⟩
  · apply local_refinement
    intro σ
    cases σ with
    | inl σ => exact ⟨σ.val, Set.Subset.rfl⟩
    | inr σ => exact ⟨σ.val, Set.Subset.rfl⟩

/-- The actual zero-new-coordinate slice on genuine simplicial cochains. -/
def zeroNewCoordinates (n : ℕ) : Cochain K n G →+ Cochain K n G :=
  project (actualCoordinates K p n)

@[simp] theorem zeroNewCoordinates_old (n : ℕ) (c : Cochain K n G)
    (τ : Simplex K n) (hτ : p ∉ τ.val) : zeroNewCoordinates K p n c τ = c τ :=
  project_mem _ _ hτ

@[simp] theorem zeroNewCoordinates_new (n : ℕ) (c : Cochain K n G)
    (τ : Simplex K n) (hτ : p ∈ τ.val) : zeroNewCoordinates K p n c τ = 0 :=
  project_not_mem _ _ (fun h => h hτ)

/-- The locality part of Theorem 4.3 with the actual simplicial zero slice:
the actual term and normalized cap term are local on their respective sides. -/
theorem simplicial_local_iff_zero_slice [Nonempty (ActualFacet K p)] (n : ℕ)
    (f : Cochain K n G → P) :
    AnchoredLocal (fun σ : NonemptySimplex K => facesIn K n σ) f ↔
      AnchoredLocal (actualFacets K p n) (fun c => f (zeroNewCoordinates K p n c)) ∧
      AnchoredLocal (capFacets K p n) (fun c => f c - f (zeroNewCoordinates K p n c)) := by
  rw [local_all_iff_split K p n]
  exact local_iff_normalized_slices (actualFacets K p n) (capFacets K p n)
    (actualCoordinates K p n) (actualFacet_inside K p n) (cap_boundary_in_actual K p n) f

/-- The simplicial split is uniquely determined by the cap normalization,
even before imposing closed-cochain invariance. -/
theorem simplicial_zero_slice_unique (n : ℕ) (f φ χ : Cochain K n G → P)
    (hφ : AnchoredLocal (actualFacets K p n) φ)
    (hzero : ∀ c, χ (zeroNewCoordinates K p n c) = 0) (hsplit : f = φ + χ) :
    φ = (fun c => f (zeroNewCoordinates K p n c)) ∧
      χ = (fun c => f c - f (zeroNewCoordinates K p n c)) :=
  normalized_split_unique (actualFacets K p n) (actualCoordinates K p n)
    (actualFacet_inside K p n) f φ χ hφ hzero hsplit

end OpenDisk.BulkPhaseSimplicialGluing
