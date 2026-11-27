import Formalization.Section3SimplexLocalTau
import Formalization.Section3SquareStripLocality

set_option linter.style.header false

/-!
# Section 3: local elementary cubes act by replacement identities

Fix an elementary label t.  Its visible facets form the carrier family used
by the local-tau lemma.  A local elementary nonface cube has two kinds of
facets: outside the carrier, t itself vanishes; inside the carrier, one of the
cube labels vanishes.  Thus t together with all cube labels satisfies the
global no-common-facet condition.  The square-strip theorem then sends the
cube to the full physical identity denominator.
-/

noncomputable section

namespace GeneralSphereT.PathAlgebra

universe uF uB

variable {ι G B : Type*}
variable [LinearOrder ι] [AddCommGroup G] [AddCommGroup B]
variable {Facet : Type uF}
variable {BAt : Facet → Type uB} [∀ ρ, AddCommGroup (BAt ρ)]
variable {facets : Facet → Set ι}
variable {d : Configuration ι G →+ B}

variable (L : FacetRestrictionData
  (CAt := fun ρ => Configuration (facets ρ) G)
  (BAt := BAt) (Facet := Facet) d)

/-- The facets on which a fixed complete operator label survives. -/
abbrev OperatorVisibleFacet (t : Configuration ι G) :=
  {ρ : Facet // L.primitiveRes ρ t ≠ 0}

/-- Coordinate sets of the visible-facet carrier family. -/
def operatorVisibleFacetSets (t : Configuration ι G) :
    OperatorVisibleFacet L t → Set ι :=
  fun ρ => facets ρ.1

/-- Restrict the linearized replacement error to augmentation-zero base
distributions. -/
def ellRedDistribution (t : Configuration ι G)
    (word : List (Configuration ι G)) :
    RedDist B →ₗ[ℤ] Path (Configuration ι G) B :=
  (ellDistribution d t word).comp (RedDist B).subtype

omit [LinearOrder ι] in
@[simp]
theorem ellRedDistribution_coe
    (t : Configuration ι G) (word : List (Configuration ι G))
    (z : RedDist B) :
    ellRedDistribution (d := d) t word z =
      ellDistribution d t word z.1 :=
  rfl

section ArbitraryCarrierFamily

universe uL

variable {LocalFacet : Type uL}
variable {localFacets : LocalFacet → Set ι}

/-- Generator form for an arbitrary carrier family embedded in the global
facet family.  Every globally visible facet must occur in that family. -/
theorem ellRedDistribution_elementaryCarrierCubeGenerator_mem
    (hprimitive : ∀ ρ : Facet,
      L.primitiveRes ρ = coordinateRestriction (facets ρ))
    (embed : LocalFacet → Facet)
    (hfacets : ∀ lf : LocalFacet, localFacets lf = facets (embed lf))
    (t : Configuration ι G) (word : List (Configuration ι G))
    (ht : IsElementaryLabel t)
    (hword : ∀ u ∈ word, IsElementaryLabel u)
    (hendpoint : d (wordIncrement word) = d t)
    (hvisibility : ∀ u ∈ word, ∀ ρ : Facet,
      L.primitiveRes ρ u ≠ 0 → L.primitiveRes ρ t ≠ 0)
    (hcarrier : ∀ ρ : Facet, L.primitiveRes ρ t ≠ 0 →
      ∃ lf : LocalFacet, embed lf = ρ)
    {z : RedDist B}
    (hz : z ∈ elementaryPhysicalNonfaceCubeGenerators localFacets d) :
    ellRedDistribution (d := d) t word z ∈
      physicalIdentityPaths L := by
  rcases hz with ⟨steps, hsteps, a, helem, hcover, rfl⟩
  cases steps with
  | nil => exact (hsteps rfl).elim
  | cons r rs =>
      have hr : IsElementaryLabel r := helem r (by simp)
      have hcommon :
          NoCommonFacetList L.primitiveRes (t :: r :: rs) := by
        rw [noCommonFacetList_iff]
        intro ρ
        by_cases htρ : L.primitiveRes ρ t = 0
        · exact ⟨t, by simp, htρ⟩
        · obtain ⟨lf, hlf⟩ := hcarrier ρ htρ
          obtain ⟨s, hs, hszero⟩ := hcover lf
          refine ⟨s, by simp [hs], ?_⟩
          rw [← hlf, hprimitive (embed lf), ← hfacets lf]
          exact hszero
      change ellDistribution d t word
          (physicalNonfaceCube d (r :: rs) (by simp) a).1 ∈
        physicalIdentityPaths L
      rw [physicalNonfaceCube_coe]
      exact ellDistribution_elementaryCube_mem_physicalIdentityPaths
        L t r word rs a ht hr
          (fun u hu => hword u hu) hendpoint hvisibility hcommon

/-- Span form for an arbitrary embedded carrier family. -/
theorem ellRedDistribution_elementaryCarrierCubeSpan_mem
    (hprimitive : ∀ ρ : Facet,
      L.primitiveRes ρ = coordinateRestriction (facets ρ))
    (embed : LocalFacet → Facet)
    (hfacets : ∀ lf : LocalFacet, localFacets lf = facets (embed lf))
    (t : Configuration ι G) (word : List (Configuration ι G))
    (ht : IsElementaryLabel t)
    (hword : ∀ u ∈ word, IsElementaryLabel u)
    (hendpoint : d (wordIncrement word) = d t)
    (hvisibility : ∀ u ∈ word, ∀ ρ : Facet,
      L.primitiveRes ρ u ≠ 0 → L.primitiveRes ρ t ≠ 0)
    (hcarrier : ∀ ρ : Facet, L.primitiveRes ρ t ≠ 0 →
      ∃ lf : LocalFacet, embed lf = ρ)
    {z : RedDist B}
    (hz : z ∈ elementaryPhysicalNonfaceCubeSpan localFacets d) :
    ellRedDistribution (d := d) t word z ∈
      physicalIdentityPaths L := by
  induction hz using Submodule.span_induction with
  | mem z hz =>
      exact ellRedDistribution_elementaryCarrierCubeGenerator_mem
        L hprimitive embed hfacets t word ht hword hendpoint hvisibility
          hcarrier hz
  | zero => simp
  | add x y hx hy ihx ihy =>
      simpa using Submodule.add_mem (physicalIdentityPaths L) ihx ihy
  | smul n x hx ih =>
      simpa using Submodule.smul_mem (physicalIdentityPaths L) n ih

end ArbitraryCarrierFamily

/-- One generator of the elementary local-cube span is sent to a global
physical identity by the square-strip replacement error. -/
theorem ellRedDistribution_elementaryLocalCubeGenerator_mem
    (hprimitive : ∀ ρ : Facet,
      L.primitiveRes ρ = coordinateRestriction (facets ρ))
    (t : Configuration ι G) (word : List (Configuration ι G))
    (ht : IsElementaryLabel t)
    (hword : ∀ u ∈ word, IsElementaryLabel u)
    (hendpoint : d (wordIncrement word) = d t)
    (hvisibility : ∀ u ∈ word, ∀ ρ : Facet,
      L.primitiveRes ρ u ≠ 0 → L.primitiveRes ρ t ≠ 0)
    {z : RedDist B}
    (hz : z ∈ elementaryPhysicalNonfaceCubeGenerators
      (operatorVisibleFacetSets L t) d) :
    ellRedDistribution (d := d) t word z ∈
      physicalIdentityPaths L := by
  rcases hz with ⟨steps, hsteps, a, helem, hcover, rfl⟩
  cases steps with
  | nil => exact (hsteps rfl).elim
  | cons r rs =>
      have hr : IsElementaryLabel r := helem r (by simp)
      have hcommon :
          NoCommonFacetList L.primitiveRes (t :: r :: rs) := by
        rw [noCommonFacetList_iff]
        intro ρ
        by_cases htρ : L.primitiveRes ρ t = 0
        · exact ⟨t, by simp, htρ⟩
        · obtain ⟨s, hs, hszero⟩ := hcover ⟨ρ, htρ⟩
          refine ⟨s, ?_, ?_⟩
          · simp [hs]
          · rw [hprimitive ρ]
            exact hszero
      change ellDistribution d t word
          (physicalNonfaceCube d (r :: rs) (by simp) a).1 ∈
        physicalIdentityPaths L
      rw [physicalNonfaceCube_coe]
      exact ellDistribution_elementaryCube_mem_physicalIdentityPaths
        L t r word rs a ht hr
          (fun u hu => hword u hu) hendpoint hvisibility hcommon

/-- The whole elementary local-cube span is sent into the physical identity
denominator. -/
theorem ellRedDistribution_elementaryLocalCubeSpan_mem
    (hprimitive : ∀ ρ : Facet,
      L.primitiveRes ρ = coordinateRestriction (facets ρ))
    (t : Configuration ι G) (word : List (Configuration ι G))
    (ht : IsElementaryLabel t)
    (hword : ∀ u ∈ word, IsElementaryLabel u)
    (hendpoint : d (wordIncrement word) = d t)
    (hvisibility : ∀ u ∈ word, ∀ ρ : Facet,
      L.primitiveRes ρ u ≠ 0 → L.primitiveRes ρ t ≠ 0)
    {z : RedDist B}
    (hz : z ∈ elementaryPhysicalNonfaceCubeSpan
      (operatorVisibleFacetSets L t) d) :
    ellRedDistribution (d := d) t word z ∈
      physicalIdentityPaths L := by
  induction hz using Submodule.span_induction with
  | mem z hz =>
      exact ellRedDistribution_elementaryLocalCubeGenerator_mem
        L hprimitive t word ht hword hendpoint hvisibility hz
  | zero => simp
  | add x y hx hy ihx ihy =>
      simpa using Submodule.add_mem (physicalIdentityPaths L) ihx ihy
  | smul n x hx ih =>
      simpa using Submodule.smul_mem (physicalIdentityPaths L) n ih

end GeneralSphereT.PathAlgebra
