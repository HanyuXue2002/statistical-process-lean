import Formalization.Section3ApexFreeCoboundary
import Formalization.Section3BottomOperators
import Formalization.Section3SimplicialConeReplacement

set_option linter.style.header false

/-!
# Section 3: the bottom-operator lemma on a simplicial cone

This file instantiates `BottomSectionData` for the concrete cone model.
The bottom submodule consists of global degree-`n` cochains which vanish on
every simplex containing the cone apex.  Restriction to the full apex closed
star identifies it with the closed-star apex-free submodule from
`Section3ApexFreeCoboundary`.

The inverse of the coboundary on this submodule is the cone homotopy.  Its
restriction to every simplex containing the apex is the corresponding local
cone homotopy, so the resulting section is compatible with all facets in
`coneFacetRestrictionData`.  This works uniformly in degree zero.
-/

noncomputable section

namespace GeneralSphereT.SimplicialCochain

open GeneralSphereT.PathAlgebra
open GeneralSphereT.PathAlgebra.BottomSectionData

variable {V G : Type*} [LinearOrder V] [Fintype V] [AddCommGroup G]
variable (K : AbstractSimplicialComplex V)

/-- Path algebra only needs an ordering of the finite cochain-coordinate
type; this choice is unrelated to the orientation order on vertices. -/
local instance simplicialBottomSimplexLinearOrder (n : ℕ) :
    LinearOrder (Simplex K n) := by
  classical
  exact linearOrderOfSTO WellOrderingRel

/-! ## Global apex-free cochains -/

/-- Global cochains which vanish on every simplex containing `v`. -/
def simplicialApexFreeCochains (v : V) (n : ℕ) :
    Submodule ℤ (Cochain K n G) where
  carrier := {c | ∀ σ, v ∈ σ.1 → c σ = 0}
  zero_mem' := by
    intro σ _
    rfl
  add_mem' := by
    intro c c' hc hc' σ hvσ
    simp [hc σ hvσ, hc' σ hvσ]
  smul_mem' := by
    intro z c hc σ hvσ
    simp [hc σ hvσ]

omit [LinearOrder V] [Fintype V] in
@[simp]
theorem mem_simplicialApexFreeCochains
    (v : V) (n : ℕ) (c : Cochain K n G) :
    c ∈ simplicialApexFreeCochains (G := G) K v n ↔
      ∀ σ, v ∈ σ.1 → c σ = 0 :=
  Iff.rfl

omit [LinearOrder V] [Fintype V] in
/-- The submodule predicate agrees with the support formulation used by the
simultaneous replacement theorem. -/
theorem mem_simplicialApexFreeCochains_iff_apexFreeLabel
    (v : V) (n : ℕ) (c : Cochain K n G) :
    c ∈ simplicialApexFreeCochains (G := G) K v n ↔
      ApexFreeLabel K v c := by
  classical
  constructor
  · intro hc σ hσ hvσ
    exact Finsupp.mem_support_iff.mp hσ (hc σ hvσ)
  · intro hc σ hvσ
    by_contra hne
    exact hc σ (Finsupp.mem_support_iff.mpr hne) hvσ

/-- Restricting a global apex-free cochain to the apex closed star remains
apex-free. -/
theorem restrictClosedStar_mem_apexFree
    (v : V) (n : ℕ) {c : Cochain K n G}
    (hc : c ∈ simplicialApexFreeCochains (G := G) K v n) :
    restrictClosedStar K (coneApexSimplex K v) n c ∈
      apexFreeCochains (G := G) K (coneApexSimplex K v) v n := by
  intro σ hvσ
  exact hc σ.1 hvσ

/-! ## Restricting global coboundaries to the apex closed star -/

/-- A global coboundary restricts to a coboundary on the apex closed star. -/
def restrictConeCoboundaryToRange (v : V) (n : ℕ) :
    CoboundaryGroup (G := G) K n →ₗ[ℤ]
      closedStarCoboundaryGroup (G := G) K (coneApexSimplex K v) n :=
  LinearMap.codRestrict
    (closedStarCoboundary (G := G) K (coneApexSimplex K v) n).range
    ((restrictClosedStar K (coneApexSimplex K v) (n + 1)).comp
      (coboundary K n).range.subtype)
    (fun a => by
      rcases a.2 with ⟨c, hc⟩
      refine ⟨restrictClosedStar K (coneApexSimplex K v) n c, ?_⟩
      calc
        closedStarCoboundary K (coneApexSimplex K v) n
            (restrictClosedStar K (coneApexSimplex K v) n c) =
          restrictClosedStar K (coneApexSimplex K v) (n + 1)
            (coboundary K n c) :=
          (LinearMap.congr_fun
            (restrictClosedStar_coboundary (G := G) K
              (coneApexSimplex K v) n) c).symm
        _ = restrictClosedStar K (coneApexSimplex K v) (n + 1) a.1 := by
          rw [hc])

@[simp]
theorem restrictConeCoboundaryToRange_coe
    (v : V) (n : ℕ) (a : CoboundaryGroup (G := G) K n) :
    (restrictConeCoboundaryToRange K v n a :
        ClosedStarCochain K (coneApexSimplex K v) (n + 1) G) =
      restrictClosedStar K (coneApexSimplex K v) (n + 1) a.1 :=
  rfl

/-! ## The canonical global bottom section -/

/-- The global apex-free primitive obtained by the cone homotopy. -/
def simplicialConePrimitiveRaw (v : V) (n : ℕ) :
    CoboundaryGroup (G := G) K n →ₗ[ℤ] Cochain K n G :=
  (extendCarrierClosedStar K (coneApexSimplex K v) n).toIntLinearMap.comp
    ((apexFreeCochains (G := G) K (coneApexSimplex K v) v n).subtype.comp
      ((conePrimitiveOfCoboundary K (coneApexSimplex K v) v
        (mem_coneApexSimplex K v) n).comp
        (restrictConeCoboundaryToRange K v n)))

@[simp]
theorem simplicialConePrimitiveRaw_apply
    (v : V) (n : ℕ) (a : CoboundaryGroup (G := G) K n) :
    simplicialConePrimitiveRaw K v n a =
      extendCarrierClosedStar K (coneApexSimplex K v) n
        (conePrimitiveOfCoboundary K (coneApexSimplex K v) v
          (mem_coneApexSimplex K v) n
          (restrictConeCoboundaryToRange K v n a)) :=
  rfl

/-- The canonical primitive has no simplex coordinate containing the apex. -/
theorem simplicialConePrimitiveRaw_mem_apexFree
    {v : V} (hcone : IsConeAt K v) (n : ℕ)
    (a : CoboundaryGroup (G := G) K n) :
    simplicialConePrimitiveRaw K v n a ∈
      simplicialApexFreeCochains (G := G) K v n := by
  intro σ hvσ
  let p := conePrimitiveOfCoboundary K (coneApexSimplex K v) v
    (mem_coneApexSimplex K v) n
    (restrictConeCoboundaryToRange K v n a)
  let σStar : ClosedStarSimplex K (coneApexSimplex K v) n :=
    ⟨σ, simplex_mem_apexClosedStar K hcone σ⟩
  calc
    simplicialConePrimitiveRaw K v n a σ =
        restrictClosedStar K (coneApexSimplex K v) n
          (simplicialConePrimitiveRaw K v n a) σStar := rfl
    _ = p.1 σStar := by
      simp [simplicialConePrimitiveRaw_apply, p]
    _ = 0 := p.2 σStar hvσ

/-- The canonical bottom section, with the apex-free condition in its
codomain. -/
def simplicialConePrimitive {v : V} (hcone : IsConeAt K v) (n : ℕ) :
    CoboundaryGroup (G := G) K n →ₗ[ℤ]
      simplicialApexFreeCochains (G := G) K v n :=
  LinearMap.codRestrict (simplicialApexFreeCochains (G := G) K v n)
    (simplicialConePrimitiveRaw K v n)
    (simplicialConePrimitiveRaw_mem_apexFree K hcone n)

@[simp]
theorem simplicialConePrimitive_coe
    {v : V} (hcone : IsConeAt K v) (n : ℕ)
    (a : CoboundaryGroup (G := G) K n) :
    (simplicialConePrimitive K hcone n a : Cochain K n G) =
      simplicialConePrimitiveRaw K v n a :=
  rfl

/-- On a cone, the canonical apex-free primitive has the prescribed global
coboundary. -/
theorem coboundaryToRange_simplicialConePrimitive
    {v : V} (hcone : IsConeAt K v) (n : ℕ)
    (a : CoboundaryGroup (G := G) K n) :
    coboundaryToRange (G := G) K n
        (simplicialConePrimitive K hcone n a : Cochain K n G) = a := by
  apply Subtype.ext
  apply restrictClosedStar_apex_injective (G := G) K hcone (n + 1)
  let aStar := restrictConeCoboundaryToRange K v n a
  let pStar := conePrimitiveOfCoboundary K (coneApexSimplex K v) v
    (mem_coneApexSimplex K v) n aStar
  have hinverse :
      apexFreeCoboundaryToRange K (coneApexSimplex K v) v n pStar =
        aStar :=
    apexFreeCoboundaryToRange_conePrimitiveOfCoboundary
      K (coneApexSimplex K v) v (mem_coneApexSimplex K v) n aStar
  have hinverseCoe := congrArg Subtype.val hinverse
  calc
    restrictClosedStar K (coneApexSimplex K v) (n + 1)
        (coboundary K n
          (simplicialConePrimitive K hcone n a : Cochain K n G)) =
      closedStarCoboundary K (coneApexSimplex K v) n
        (restrictClosedStar K (coneApexSimplex K v) n
          (simplicialConePrimitive K hcone n a : Cochain K n G)) :=
      LinearMap.congr_fun
        (restrictClosedStar_coboundary (G := G) K
          (coneApexSimplex K v) n)
        (simplicialConePrimitive K hcone n a : Cochain K n G)
    _ = closedStarCoboundary K (coneApexSimplex K v) n pStar.1 := by
      rw [simplicialConePrimitive_coe K hcone,
        simplicialConePrimitiveRaw_apply,
        restrictClosedStar_extendCarrierClosedStar]
    _ = aStar.1 := hinverseCoe
    _ = restrictClosedStar K (coneApexSimplex K v) (n + 1) a.1 := rfl

/-! ## Injectivity on the bottom -/

/-- Coboundary is injective on global apex-free cochains of a cone. -/
theorem coboundaryToRange_injective_on_simplicialApexFree
    {v : V} (hcone : IsConeAt K v) (n : ℕ) :
    Function.Injective
      ((coboundaryToRange (G := G) K n).comp
        (simplicialApexFreeCochains (G := G) K v n).subtype.toAddMonoidHom) := by
  intro c c' hdc
  apply Subtype.ext
  apply restrictClosedStar_apex_injective (G := G) K hcone n
  apply closedStarCoboundary_injective_on_apexFree
    K (coneApexSimplex K v) v (mem_coneApexSimplex K v) n
  · exact restrictClosedStar_mem_apexFree K v n c.2
  · exact restrictClosedStar_mem_apexFree K v n c'.2
  · have hglobal : coboundary K n c.1 = coboundary K n c'.1 :=
      congrArg Subtype.val hdc
    calc
      closedStarCoboundary K (coneApexSimplex K v) n
          (restrictClosedStar K (coneApexSimplex K v) n c.1) =
        restrictClosedStar K (coneApexSimplex K v) (n + 1)
          (coboundary K n c.1) :=
        (LinearMap.congr_fun
          (restrictClosedStar_coboundary (G := G) K
            (coneApexSimplex K v) n) c.1).symm
      _ = restrictClosedStar K (coneApexSimplex K v) (n + 1)
          (coboundary K n c'.1) := by rw [hglobal]
      _ = closedStarCoboundary K (coneApexSimplex K v) n
          (restrictClosedStar K (coneApexSimplex K v) n c'.1) :=
        LinearMap.congr_fun
          (restrictClosedStar_coboundary (G := G) K
            (coneApexSimplex K v) n) c'.1

/-! ## Compatibility with every apex-containing facet -/

/-- Restricting the global cone primitive to an apex-containing simplex is
the local simplex cone primitive. -/
theorem restrictFacet_simplicialConePrimitive
    {v : V} (hcone : IsConeAt K v) (n : ℕ) (ρ : ConeFacet K v)
    (a : CoboundaryGroup (G := G) K n) :
    coordinateRestriction (facesIn K n ρ.1)
        (simplicialConePrimitive K hcone n a : Cochain K n G) =
      simplexConeHomotopy K (coneApexSimplex K v) ρ.1 ρ.2 v
        (mem_coneApexSimplex K v) n
        (restrictCoboundary K n ρ.1 a) := by
  let aStar := restrictConeCoboundaryToRange K v n a
  have hrestrict :
      restrictClosedStarToSimplex K (coneApexSimplex K v) ρ.1 ρ.2
          (n + 1) aStar.1 =
        restrictCoboundary K n ρ.1 a := by
    ext τ
    rfl
  ext τ
  calc
    coordinateRestriction (facesIn K n ρ.1)
        (simplicialConePrimitive K hcone n a : Cochain K n G) τ =
      restrictClosedStarToSimplex K (coneApexSimplex K v) ρ.1 ρ.2 n
        (restrictClosedStar K (coneApexSimplex K v) n
          (simplicialConePrimitive K hcone n a : Cochain K n G)) τ := by
      rfl
    _ = restrictClosedStarToSimplex K (coneApexSimplex K v) ρ.1 ρ.2 n
        (coneHomotopy K (coneApexSimplex K v) v
          (mem_coneApexSimplex K v) n aStar.1) τ := by
      rw [simplicialConePrimitive_coe K hcone,
        simplicialConePrimitiveRaw_apply,
        restrictClosedStar_extendCarrierClosedStar,
        conePrimitiveOfCoboundary_coe]
    _ = simplexConeHomotopy K (coneApexSimplex K v) ρ.1 ρ.2 v
        (mem_coneApexSimplex K v) n
        (restrictClosedStarToSimplex K (coneApexSimplex K v) ρ.1 ρ.2
          (n + 1) aStar.1) τ := by
      exact DFunLike.congr_fun
        (LinearMap.congr_fun
          (restrictClosedStarToSimplex_coneHomotopy
            (G := G) K (coneApexSimplex K v) ρ.1 ρ.2 v
              (mem_coneApexSimplex K v) n) aStar.1) τ
    _ = simplexConeHomotopy K (coneApexSimplex K v) ρ.1 ρ.2 v
        (mem_coneApexSimplex K v) n
        (restrictCoboundary K n ρ.1 a) τ := by
      rw [hrestrict]

/-! ## The concrete `BottomSectionData` -/

/-- The cone homotopy packages the global and all local bottom sections. -/
def simplicialConeBottomSectionData
    {v : V} (hcone : IsConeAt K v) (n : ℕ) :
    BottomSectionData
      (L := coneFacetRestrictionData (G := G) K v n)
      (simplicialApexFreeCochains (G := G) K v n) where
  baseSection := (simplicialConePrimitive K hcone n).toAddMonoidHom
  rightInverse := by
    apply AddMonoidHom.ext
    intro a
    exact coboundaryToRange_simplicialConePrimitive K hcone n a
  injectiveOnBottom :=
    coboundaryToRange_injective_on_simplicialApexFree K hcone n
  localSection ρ :=
    (simplexConeHomotopy K (coneApexSimplex K v) ρ.1 ρ.2 v
      (mem_coneApexSimplex K v) n).toAddMonoidHom
  restrict_section ρ := by
    apply AddMonoidHom.ext
    intro a
    exact restrictFacet_simplicialConePrimitive K hcone n ρ a

/-! ## Coverage and the concrete bottom conclusion -/

omit [Fintype V] in
/-- Every degree-`n` simplex is visible in an apex-containing simplex of a
cone. -/
theorem coneFacetRestrictionData_cover
    {v : V} (hcone : IsConeAt K v) (n : ℕ) :
    ∀ τ : Simplex K n,
      ∃ ρ : ConeFacet K v,
        τ ∈ carrierFacetSets K (coneApexSimplex K v) n ρ := by
  intro τ
  let σ : NonemptySimplex K :=
    ⟨insert v τ.1, hcone ⟨τ.1, τ.2.1⟩⟩
  let ρ : ConeFacet K v := ⟨σ, by
    intro x hx
    have hxv : x = v := by simpa [coneApexSimplex] using hx
    subst x
    simp [σ]⟩
  refine ⟨ρ, ?_⟩
  intro x hx
  exact Finset.mem_insert_of_mem hx

/-- If an invariant path on a simplicial cone already uses only apex-free
complete labels, then it belongs to the physical identity submodule. -/
theorem mem_physicalIdentityPaths_of_apexFree_labels
    {v : V} (hcone : IsConeAt K v) (n : ℕ)
    {e : Path (Cochain K n G) (CoboundaryGroup (G := G) K n)}
    (he : e ∈ physicalInvariantPaths
      (coneFacetRestrictionData (G := G) K v n))
    (hlabels : e ∈ restrictedElementaryPaths
      (B := CoboundaryGroup (G := G) K n) (ApexFreeLabel K v)) :
    e ∈ physicalIdentityPaths
      (coneFacetRestrictionData (G := G) K v n) := by
  have hlabels' : e ∈ restrictedElementaryPaths
      (B := CoboundaryGroup (G := G) K n)
      (fun r => r ∈ simplicialApexFreeCochains (G := G) K v n) := by
    rw [restrictedElementaryPaths] at hlabels ⊢
    refine Submodule.span_mono ?_ hlabels
    rintro p ⟨r, a, hr, hfree, rfl⟩
    exact ⟨r, a, hr,
      (mem_simplicialApexFreeCochains_iff_apexFreeLabel
        (G := G) K v n r).2 hfree, rfl⟩
  exact mem_physicalIdentityPaths_of_labels_mem_bottom
    (facets := carrierFacetSets K (coneApexSimplex K v) n)
    (L := coneFacetRestrictionData (G := G) K v n)
    (simplicialApexFreeCochains (G := G) K v n)
    (simplicialConeBottomSectionData K hcone n)
    (carrierFacetRestrictionData_primitiveRes
      (G := G) K (coneApexSimplex K v) n)
    (coneFacetRestrictionData_cover K hcone n)
    he hlabels'

end GeneralSphereT.SimplicialCochain
