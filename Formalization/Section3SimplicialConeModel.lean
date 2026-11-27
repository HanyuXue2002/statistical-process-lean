import Formalization.Section3SimplicialConeReplacement
import Formalization.Section3SimplicialBottomOperators
import Formalization.Section3PathFacetRefinement
import Mathlib.Data.Fintype.WithTopBot
import Mathlib.Order.WithBot

set_option linter.style.header false

/-!
# Section 3: the literal simplicial cone `C_v M`

Mathlib's current `AbstractSimplicialComplex` API has maps and lattice
operations, but no join or cone constructor.  This file supplies only the
small construction needed here.  The vertices of the cone on `M` are
`Option V`: `none` is the new apex and `some x` is the old vertex `x`.

A nonempty finite set is a cone face exactly when, after deleting the apex
and unwrapping the remaining vertices, its base is either empty (the apex
singleton) or a face of `M`.  We prove that adjoining `none` preserves every
face, identify the embedded bottom, and state simultaneous apex replacement
directly for this literal cone rather than for an abstract `IsConeAt`
hypothesis.
-/

noncomputable section

namespace GeneralSphereT.SimplicialCochain

open GeneralSphereT.PathAlgebra
open GeneralSphereT.PathAlgebra.FacetRestrictionData

variable {V G : Type*}

local instance coneVertexDecidableEq : DecidableEq V := Classical.decEq V

/-! ## Faces of the cone -/

/-- Delete the apex from an `Option V`-finset and unwrap all remaining
vertices. -/
def coneBaseVertices (s : Finset (Option V)) : Finset V :=
  s.filterMap id (by
    intro a a' b ha ha'
    exact ha.trans ha'.symm)

@[simp]
theorem mem_coneBaseVertices (s : Finset (Option V)) (x : V) :
    x ∈ coneBaseVertices s ↔ some x ∈ s := by
  simp [coneBaseVertices]

theorem coneBaseVertices_mono {s t : Finset (Option V)} (hst : s ⊆ t) :
    coneBaseVertices s ⊆ coneBaseVertices t := by
  intro x hx
  rw [mem_coneBaseVertices] at hx ⊢
  exact hst hx

@[simp]
theorem coneBaseVertices_insert_apex (s : Finset (Option V)) :
    coneBaseVertices (insert (none : Option V) s) = coneBaseVertices s := by
  ext x
  simp

@[simp]
theorem coneBaseVertices_image_some (s : Finset V) :
    coneBaseVertices (s.image some) = s := by
  ext x
  simp

@[simp]
theorem coneBaseVertices_singleton_apex :
    coneBaseVertices ({none} : Finset (Option V)) = ∅ := by
  ext x
  rw [mem_coneBaseVertices]
  simp

@[simp]
theorem coneBaseVertices_singleton_some (x : V) :
    coneBaseVertices ({some x} : Finset (Option V)) = {x} := by
  ext y
  rw [mem_coneBaseVertices]
  simp

/-- The simplicial cone on `M`, with new apex `none`. -/
def simplicialCone (M : AbstractSimplicialComplex V) :
    AbstractSimplicialComplex (Option V) where
  faces := {s | s.Nonempty ∧
    (coneBaseVertices s = ∅ ∨ coneBaseVertices s ∈ M)}
  isRelLowerSet_faces := by
    intro s hs
    refine ⟨hs.1, ?_⟩
    intro t hts ht
    refine ⟨ht, ?_⟩
    have hbase : coneBaseVertices t ⊆ coneBaseVertices s :=
      coneBaseVertices_mono hts
    rcases hs.2 with hs0 | hsM
    · left
      exact Finset.Subset.antisymm
        (hbase.trans (by simp [hs0])) (Finset.empty_subset _)
    · by_cases ht0 : coneBaseVertices t = ∅
      · exact Or.inl ht0
      · exact Or.inr
          ((M.isRelLowerSet_faces hsM).2 hbase
            (Finset.nonempty_iff_ne_empty.mpr ht0))
  singleton_mem o := by
    constructor
    · exact Finset.singleton_nonempty o
    · cases o with
      | none => exact Or.inl coneBaseVertices_singleton_apex
      | some x =>
          right
          rw [coneBaseVertices_singleton_some]
          exact M.singleton_mem x

@[simp]
theorem mem_simplicialCone (M : AbstractSimplicialComplex V)
    (s : Finset (Option V)) :
    s ∈ simplicialCone M ↔
      s.Nonempty ∧
        (coneBaseVertices s = ∅ ∨ coneBaseVertices s ∈ M) :=
  Iff.rfl

/-! ## Bottom embedding -/

/-- A bottom face is obtained by applying `some` to all of its vertices. -/
def simplicialConeBottomFace (M : AbstractSimplicialComplex V)
    (σ : NonemptySimplex M) : NonemptySimplex (simplicialCone M) :=
  ⟨σ.1.image some, by
    rw [mem_simplicialCone, coneBaseVertices_image_some]
    exact ⟨Finset.image_nonempty.mpr
      ((M.isRelLowerSet_faces σ.2).1), Or.inr σ.2⟩⟩

@[simp]
theorem simplicialConeBottomFace_val
    (M : AbstractSimplicialComplex V) (σ : NonemptySimplex M) :
    (simplicialConeBottomFace M σ).1 = σ.1.image some :=
  rfl

/-- A base finset is a face of the embedded bottom exactly when it was a
face of `M`.  Thus this is a genuine copy of `M`, not merely a face map. -/
theorem image_some_mem_simplicialCone_iff
    (M : AbstractSimplicialComplex V) (s : Finset V) :
    s.image some ∈ simplicialCone M ↔ s ∈ M := by
  rw [mem_simplicialCone, coneBaseVertices_image_some]
  constructor
  · rintro ⟨himage, hs0 | hsM⟩
    · subst s
      simp at himage
    · exact hsM
  · intro hsM
    exact ⟨Finset.image_nonempty.mpr
      ((M.isRelLowerSet_faces hsM).1), Or.inr hsM⟩

/-- The bottom-face map is injective. -/
theorem simplicialConeBottomFace_injective
    (M : AbstractSimplicialComplex V) :
    Function.Injective (simplicialConeBottomFace M) := by
  intro σ τ h
  apply Subtype.ext
  have hval := congrArg Subtype.val h
  have hbase := congrArg coneBaseVertices hval
  change coneBaseVertices (σ.1.image some) =
    coneBaseVertices (τ.1.image some) at hbase
  rw [coneBaseVertices_image_some, coneBaseVertices_image_some] at hbase
  exact hbase

/-! ## Apex condition and direct Section 3 statement for `C_v M` -/

variable [LinearOrder V] [Fintype V] [AddCommGroup G]

/-- `Option V` with `none` ordered below all old vertices.  This is the
underlying order of Mathlib's `WithBot V`, exposed on the literal `Option`
model used above. -/
local instance coneOptionLinearOrder : LinearOrder (Option V) :=
  @WithBot.linearOrder V inferInstance

omit [Fintype V] in
/-- The literal cone satisfies the precise apex condition used by the
Section 3 replacement theorem. -/
theorem simplicialCone_isConeAt (M : AbstractSimplicialComplex V) :
    IsConeAt (simplicialCone M) none := by
  letI : DecidableEq (Option V) := LinearOrder.toDecidableEq
  intro σ
  rw [mem_simplicialCone]
  refine ⟨by simp, ?_⟩
  have hσ := (mem_simplicialCone M σ.1).mp σ.2
  have hbase : coneBaseVertices (insert none σ.1) =
      coneBaseVertices σ.1 := by
    ext x
    rw [mem_coneBaseVertices, mem_coneBaseVertices]
    simp
  rw [hbase]
  exact hσ.2

/-- Simultaneous apex replacement, now stated directly on the literal
simplicial cone `C_v M`. -/
theorem simplicialCone_simultaneousApexReplacement_exists
    (M : AbstractSimplicialComplex V) (n : ℕ)
    (e : Path (Cochain (simplicialCone M) n G)
      (CoboundaryGroup (G := G) (simplicialCone M) n))
    (he : e ∈ physicalInvariantPaths
      (coneFacetRestrictionData (G := G) (simplicialCone M) none n)) :
    ∃ ebot : Path (Cochain (simplicialCone M) n G)
        (CoboundaryGroup (G := G) (simplicialCone M) n),
      ebot ∈ restrictedElementaryPaths
        (B := CoboundaryGroup (G := G) (simplicialCone M) n)
        (ApexFreeLabel (simplicialCone M) none) ∧
      e - ebot ∈ physicalIdentityPaths
        (coneFacetRestrictionData (G := G) (simplicialCone M) none n) := by
  exact simultaneousApexReplacement_exists
    (G := G) (simplicialCone M) (simplicialCone_isConeAt M) n e he

/-! ## The full cone conclusion -/

/-- On the literal cone `C_v M`, every global invariant elementary path is
already a global physical identity.  This combines simultaneous replacement,
the bottom-operator lemma, and refinement from apex facets to all simplices. -/
theorem simplicialCone_globalPhysicalInvariantPaths_le_identity
    (M : AbstractSimplicialComplex V) (n : ℕ) :
    physicalInvariantPaths
        (facetRestrictionData (G := G) (simplicialCone M) n) ≤
      physicalIdentityPaths
        (facetRestrictionData (G := G) (simplicialCone M) n) := by
  intro e he
  let hcone : IsConeAt (simplicialCone M) none :=
    simplicialCone_isConeAt M
  have heCone : e ∈ physicalInvariantPaths
      (coneFacetRestrictionData (G := G) (simplicialCone M) none n) :=
    globalPhysicalInvariantPaths_le_cone
      (G := G) (simplicialCone M) none n he
  obtain ⟨ebot, hbot, herror⟩ :=
    simultaneousApexReplacement_exists
      (G := G) (simplicialCone M) hcone n e heCone
  have herrorInv : e - ebot ∈ physicalInvariantPaths
      (coneFacetRestrictionData (G := G) (simplicialCone M) none n) :=
    physicalIdentityPaths_le_physicalInvariantPaths
      (coneFacetRestrictionData (G := G) (simplicialCone M) none n) herror
  have hebotInv : ebot ∈ physicalInvariantPaths
      (coneFacetRestrictionData (G := G) (simplicialCone M) none n) := by
    have heq : ebot = e - (e - ebot) := by abel
    rw [heq]
    exact Submodule.sub_mem _ heCone herrorInv
  have hbotIdentity : ebot ∈ physicalIdentityPaths
      (coneFacetRestrictionData (G := G) (simplicialCone M) none n) :=
    mem_physicalIdentityPaths_of_apexFree_labels
      (G := G) (simplicialCone M) hcone n hebotInv hbot
  have heConeIdentity : e ∈ physicalIdentityPaths
      (coneFacetRestrictionData (G := G) (simplicialCone M) none n) := by
    have heq : e = (e - ebot) + ebot := by abel
    rw [heq]
    exact Submodule.add_mem _ herror hbotIdentity
  exact conePhysicalIdentityPaths_le_global
    (G := G) (simplicialCone M) hcone n heConeIdentity

/-- Representative form of `T(C_v M)=0` for the full simplicial facet
presentation used in Section 2. -/
theorem simplicialConePhysicalQuotient_eq_zero
    (M : AbstractSimplicialComplex V) (n : ℕ)
    (x : PhysicalQuotient
      (facetRestrictionData (G := G) (simplicialCone M) n)) :
    x = 0 := by
  refine Submodule.Quotient.induction_on
    (p := physicalIdentityPathsInInvariantPaths
      (facetRestrictionData (G := G) (simplicialCone M) n)) x ?_
  intro e
  apply (Submodule.Quotient.mk_eq_zero
    (physicalIdentityPathsInInvariantPaths
      (facetRestrictionData (G := G) (simplicialCone M) n))).2
  change (e : Path (Cochain (simplicialCone M) n G)
      (CoboundaryGroup (G := G) (simplicialCone M) n)) ∈
    physicalIdentityPaths
      (facetRestrictionData (G := G) (simplicialCone M) n)
  exact simplicialCone_globalPhysicalInvariantPaths_le_identity
    (G := G) M n e.property

/-- Typeclass form of `T(C_v M)=0`. -/
theorem simplicialConePhysicalQuotient_subsingleton
    (M : AbstractSimplicialComplex V) (n : ℕ) :
    Subsingleton
      (PhysicalQuotient
        (facetRestrictionData (G := G) (simplicialCone M) n)) :=
  ⟨fun x y =>
    (simplicialConePhysicalQuotient_eq_zero (G := G) M n x).trans
      (simplicialConePhysicalQuotient_eq_zero (G := G) M n y).symm⟩

/-- Representative form of `tau(C_v M)=0` on the literal cone. -/
theorem literalSimplicialConeTau_eq_zero
    (M : AbstractSimplicialComplex V) (n : ℕ)
    (x : Tau
      (fun σ : NonemptySimplex (simplicialCone M) =>
        facesIn (simplicialCone M) n σ)
      (facetRestrictionData (G := G) (simplicialCone M) n)) :
    x = 0 := by
  exact simplicialConeTau_eq_zero
    (G := G) (simplicialCone M) (simplicialCone_isConeAt M) n x

/-- Typeclass form of `tau(C_v M)=0`. -/
theorem literalSimplicialConeTau_subsingleton
    (M : AbstractSimplicialComplex V) (n : ℕ) :
    Subsingleton
      (Tau
        (fun σ : NonemptySimplex (simplicialCone M) =>
          facesIn (simplicialCone M) n σ)
        (facetRestrictionData (G := G) (simplicialCone M) n)) :=
  simplicialConeTau_subsingleton
    (G := G) (simplicialCone M) (simplicialCone_isConeAt M) n

end GeneralSphereT.SimplicialCochain
