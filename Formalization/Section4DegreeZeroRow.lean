import Formalization.RelativeDistributionLift
import Formalization.SimplicialFacetData
import Formalization.TauQuotient

set_option linter.style.header false

/-!
# Section 4: the algebraic degree-zero restriction row

This file isolates the algebraic content of (4.1)--(4.2), before identifying
the middle quotient with an actual simplicial mapping group.  A reduced
primitive distribution represents an `F`-valued compatible local section
exactly when its physical pushforward is facetwise zero.  We quotient such
representatives by the primitive distributions which are already facetwise
zero, and obtain the exact row

`Zprim -> Rprim -> StrictFSections -> Tau`.

The only two hypotheses needed for exactness at the last two terms are the
already familiar distribution identity image equality and surjectivity of
physical pushforward.  The end of the file supplies these hypotheses for the
finite ordered simplicial cochain model.
-/

noncomputable section

namespace GeneralSphereT.PathAlgebra

universe uF uC uB

namespace FacetRestrictionData

section StrictSections

variable {C B : Type*} [AddCommGroup C] [AddCommGroup B]
variable {Facet : Type uF}
variable {CAt : Facet → Type uC} {BAt : Facet → Type uB}
variable [∀ ρ, AddCommGroup (CAt ρ)] [∀ ρ, AddCommGroup (BAt ρ)]
variable {d : C →+ B}

variable (L : FacetRestrictionData
  (CAt := CAt) (BAt := BAt) (Facet := Facet) d)

/-- Reduced primitive distributions whose physical pushforward is locally
zero.  These are precisely the global representatives of strict compatible
local sections with values in the kernel simplicial group `F`. -/
def fCompatibleRedDist : Submodule ℤ (RedDist C) :=
  Submodule.comap (mapRedDist d) (physicalInvariantDistributions L)

/-- Locally-zero primitive distributions, regarded inside the compatible
representatives. -/
def locallyZeroInFCompatible : Submodule ℤ (fCompatibleRedDist L) :=
  Submodule.comap (fCompatibleRedDist L).subtype (locallyZeroRedDist L)

/-- The strict group of compatible local `F`-sections, still presented
algebraically.  Its later identification with `Hom_sSet(M,F)` is deliberately
not asserted in this file. -/
abbrev StrictFSections :=
  fCompatibleRedDist L ⧸ locallyZeroInFCompatible L

/-- A primitive relation has an `F`-compatible restriction family. -/
def rprimToFCompatible :
    Rprim (d := d) →ₗ[ℤ] fCompatibleRedDist L :=
  LinearMap.codRestrict (fCompatibleRedDist L)
    (Rprim (d := d)).subtype fun r => by
      change mapRedDist d (r : RedDist C) ∈
        physicalInvariantDistributions L
      rw [LinearMap.mem_ker.mp r.property]
      exact Submodule.zero_mem _

@[simp]
theorem rprimToFCompatible_coe (r : Rprim (d := d)) :
    ((rprimToFCompatible L r : fCompatibleRedDist L) : RedDist C) = r :=
  rfl

/-- The restriction arrow from primitive relations to strict compatible
`F`-sections. -/
def restrictionClass :
    Rprim (d := d) →ₗ[ℤ] StrictFSections L :=
  (locallyZeroInFCompatible L).mkQ.comp (rprimToFCompatible L)

@[simp]
theorem restrictionClass_apply (r : Rprim (d := d)) :
    restrictionClass L r =
      (locallyZeroInFCompatible L).mkQ (rprimToFCompatible L r) :=
  rfl

/-- The inclusion of primitive cycles into primitive relations. -/
def zprimToRprim : Zprim L →ₗ[ℤ] Rprim (d := d) :=
  LinearMap.codRestrict (Rprim (d := d)) (Zprim L).subtype
    fun z => z.property.1

@[simp]
theorem zprimToRprim_coe (z : Zprim L) :
    ((zprimToRprim L z : Rprim (d := d)) : RedDist C) = z :=
  rfl

/-- The first nonzero arrow in the degree-zero row is injective. -/
theorem zprimToRprim_injective : Function.Injective (zprimToRprim L) := by
  intro x y hxy
  apply Subtype.ext
  exact congrArg (fun r : Rprim (d := d) => (r : RedDist C)) hxy

/-- Exactness at `Rprim`: a primitive relation restricts trivially exactly
when it is also locally zero. -/
theorem exact_zprimToRprim_restrictionClass :
    Function.Exact (zprimToRprim L) (restrictionClass L) := by
  intro r
  constructor
  · intro hr
    rw [restrictionClass_apply] at hr
    have hlocalF : rprimToFCompatible L r ∈
        locallyZeroInFCompatible L :=
      (Submodule.Quotient.mk_eq_zero
        (locallyZeroInFCompatible L)).1 hr
    have hlocal : (r : RedDist C) ∈ locallyZeroRedDist L := by
      exact hlocalF
    let z : Zprim L := ⟨(r : RedDist C), ⟨r.property, hlocal⟩⟩
    refine ⟨z, ?_⟩
    apply Subtype.ext
    rfl
  · rintro ⟨z, rfl⟩
    rw [restrictionClass_apply]
    apply (Submodule.Quotient.mk_eq_zero
      (locallyZeroInFCompatible L)).2
    exact z.property.2

end StrictSections

section Obstruction

variable {ι G : Type*} [LinearOrder ι] [AddCommGroup G]
variable {B : Type uB} [AddCommGroup B]
variable {Facet : Type uF} (facets : Facet → Set ι)
variable {BAt : Facet → Type uC} [∀ ρ, AddCommGroup (BAt ρ)]
variable {d : Configuration ι G →+ B}

variable (L : FacetRestrictionData
  (CAt := fun ρ => Configuration (facets ρ) G)
  (BAt := BAt) (Facet := Facet) d)

/-- Push an `F`-compatible primitive representative into the physical
locally-zero numerator. -/
def fCompatibleToPhysicalInvariant :
    fCompatibleRedDist L →ₗ[ℤ] physicalInvariantDistributions L :=
  LinearMap.codRestrict (physicalInvariantDistributions L)
    ((mapRedDist d).comp (fCompatibleRedDist L).subtype) fun u => u.property

omit [LinearOrder ι] in
@[simp]
theorem fCompatibleToPhysicalInvariant_coe (u : fCompatibleRedDist L) :
    ((fCompatibleToPhysicalInvariant facets L u :
      physicalInvariantDistributions L) : RedDist B) =
      mapRedDist d (u : RedDist (Configuration ι G)) :=
  rfl

omit [LinearOrder ι] in
/-- The distribution image equality is exactly the denominator compatibility
needed to descend physical pushforward to `Tau`. -/
theorem locallyZeroInFCompatible_le_comap_physicalDenominator
    (himage :
      Submodule.map (mapRedDist d) (locallyZeroRedDist L) =
        physicalNonfaceCubeSpan facets d) :
    locallyZeroInFCompatible L ≤
      (physicalNonfaceCubeSpanInInvariantDistributions facets L).comap
        (fCompatibleToPhysicalInvariant facets L) := by
  intro u hu
  change mapRedDist d (u : RedDist (Configuration ι G)) ∈
    physicalNonfaceCubeSpan facets d
  rw [← himage]
  exact ⟨(u : RedDist (Configuration ι G)), hu, rfl⟩

/-- The obstruction arrow.  On a representative it is `[u] ↦ [d_*u]`. -/
def obstruction
    (himage :
      Submodule.map (mapRedDist d) (locallyZeroRedDist L) =
        physicalNonfaceCubeSpan facets d) :
    StrictFSections L →ₗ[ℤ] Tau facets L :=
  (locallyZeroInFCompatible L).mapQ
    (physicalNonfaceCubeSpanInInvariantDistributions facets L)
    (fCompatibleToPhysicalInvariant facets L)
    (locallyZeroInFCompatible_le_comap_physicalDenominator
      facets L himage)

omit [LinearOrder ι] in
/-- Formula (4.2) on a bundled compatible representative. -/
@[simp]
theorem obstruction_mkQ
    (himage :
      Submodule.map (mapRedDist d) (locallyZeroRedDist L) =
        physicalNonfaceCubeSpan facets d)
    (u : fCompatibleRedDist L) :
    obstruction facets L himage
        ((locallyZeroInFCompatible L).mkQ u) =
      (physicalNonfaceCubeSpanInInvariantDistributions facets L).mkQ
        (fCompatibleToPhysicalInvariant facets L u) := by
  simpa only [obstruction, Submodule.mkQ_apply] using
    (Submodule.mapQ_apply
      (p := locallyZeroInFCompatible L)
      (q := physicalNonfaceCubeSpanInInvariantDistributions facets L)
      (fCompatibleToPhysicalInvariant facets L) u)

omit [LinearOrder ι] in
/-- Exactness at strict compatible `F`-sections. -/
theorem exact_restrictionClass_obstruction
    (himage :
      Submodule.map (mapRedDist d) (locallyZeroRedDist L) =
        physicalNonfaceCubeSpan facets d) :
    Function.Exact (restrictionClass L) (obstruction facets L himage) := by
  intro x
  refine Submodule.Quotient.induction_on
    (p := locallyZeroInFCompatible L) x ?_
  intro u
  constructor
  · intro hu
    change obstruction facets L himage
      ((locallyZeroInFCompatible L).mkQ u) = 0 at hu
    rw [obstruction_mkQ] at hu
    have hphysical : mapRedDist d
        (u : RedDist (Configuration ι G)) ∈
          physicalNonfaceCubeSpan facets d := by
      exact (Submodule.Quotient.mk_eq_zero
        (physicalNonfaceCubeSpanInInvariantDistributions facets L)).1 hu
    rw [← himage] at hphysical
    rcases hphysical with ⟨n, hnlocal, hnu⟩
    have hrker :
        (u : RedDist (Configuration ι G)) - n ∈ Rprim (d := d) := by
      rw [Rprim, LinearMap.mem_ker, map_sub, hnu]
      exact sub_self _
    let r : Rprim (d := d) :=
      ⟨(u : RedDist (Configuration ι G)) - n, hrker⟩
    refine ⟨r, ?_⟩
    rw [restrictionClass_apply]
    apply (Submodule.Quotient.eq (locallyZeroInFCompatible L)).2
    change ((u : RedDist (Configuration ι G)) - n) - u ∈
      locallyZeroRedDist L
    have hneg : -n ∈ locallyZeroRedDist L :=
      (locallyZeroRedDist L).neg_mem hnlocal
    have heq :
        ((u : RedDist (Configuration ι G)) - n) - u = -n := by
      abel
    rw [heq]
    exact hneg
  · rintro ⟨r, hr⟩
    rw [← hr, restrictionClass_apply, obstruction_mkQ]
    apply (Submodule.Quotient.mk_eq_zero
      (physicalNonfaceCubeSpanInInvariantDistributions facets L)).2
    change mapRedDist d (r : RedDist (Configuration ι G)) ∈
      physicalNonfaceCubeSpan facets d
    rw [LinearMap.mem_ker.mp r.property]
    exact Submodule.zero_mem _

omit [LinearOrder ι] in
/-- Surjectivity of the last nonzero arrow in the degree-zero row. -/
theorem obstruction_surjective
    (himage :
      Submodule.map (mapRedDist d) (locallyZeroRedDist L) =
        physicalNonfaceCubeSpan facets d)
    (hsurj : Function.Surjective (mapRedDist d)) :
    Function.Surjective (obstruction facets L himage) := by
  intro x
  refine Submodule.Quotient.induction_on
    (p := physicalNonfaceCubeSpanInInvariantDistributions facets L) x ?_
  intro z
  rcases hsurj (z : RedDist B) with ⟨u, hu⟩
  have hucompat : u ∈ fCompatibleRedDist L := by
    change mapRedDist d u ∈ physicalInvariantDistributions L
    rw [hu]
    exact z.property
  let uF : fCompatibleRedDist L := ⟨u, hucompat⟩
  refine ⟨(locallyZeroInFCompatible L).mkQ uF, ?_⟩
  rw [obstruction_mkQ]
  have huz : fCompatibleToPhysicalInvariant facets L uF = z := by
    apply Subtype.ext
    exact hu
  rw [huz]
  rfl

end Obstruction

end FacetRestrictionData

/-! ## Generic and concrete sources of the two exactness hypotheses -/

/-- A surjective map of configuration groups induces a surjective map on
augmentation-zero free distributions. -/
theorem mapRedDist_surjective_of_surjective
    {X Y : Type*} [AddCommGroup X] [AddCommGroup Y]
    (f : X →+ Y) (hf : Function.Surjective f) :
    Function.Surjective (mapRedDist f) := by
  let s : Y → X := fun y => Classical.choose (hf y)
  have hs : (f : X → Y) ∘ s = id := by
    funext y
    exact Classical.choose_spec (hf y)
  intro z
  refine ⟨mapRedDistFn s z, ?_⟩
  rw [mapRedDist_eq_mapRedDistFn, mapRedDistFn_comp_apply, hs]
  apply Subtype.ext
  change mapDistFn id z.1 = z.1
  have hid : mapDistFn (id : Y → Y) = LinearMap.id := by
    ext y
    simp
  exact LinearMap.congr_fun hid z.1

namespace FacetRestrictionData

variable {ι G : Type*} [LinearOrder ι] [AddCommGroup G]
variable {B : Type uB} [AddCommGroup B]
variable {Facet : Type uF} (facets : Facet → Set ι)
variable {BAt : Facet → Type uC} [∀ ρ, AddCommGroup (BAt ρ)]
variable {d : Configuration ι G →+ B}

variable (L : FacetRestrictionData
  (CAt := fun ρ => Configuration (facets ρ) G)
  (BAt := BAt) (Facet := Facet) d)

omit [LinearOrder ι] in
/-- Coordinate primitive restrictions identify the abstract locally-zero
submodule with the common coordinate-restriction kernel. -/
theorem locallyZeroRedDist_eq_reducedCoordinateCommonRestrictionKernel
    (hprimitive : ∀ ρ : Facet,
      L.primitiveRes ρ = coordinateRestriction (facets ρ)) :
    locallyZeroRedDist L =
      reducedCoordinateCommonRestrictionKernel (G := G) facets := by
  ext u
  rw [locallyZeroRedDist, reducedCoordinateCommonRestrictionKernel]
  simp only [Submodule.mem_iInf, LinearMap.mem_ker]
  constructor
  · intro hu ρ
    simpa [restrictRedDist, hprimitive ρ] using hu ρ
  · intro hu ρ
    simpa [restrictRedDist, hprimitive ρ] using hu ρ

/-- The concrete form of the denominator image hypothesis, obtained directly
from distribution-level Lemma 2.25. -/
theorem map_locallyZeroRedDist_eq_physicalNonfaceCubeSpan
    (hprimitive : ∀ ρ : Facet,
      L.primitiveRes ρ = coordinateRestriction (facets ρ))
    (hd : Function.Surjective d) :
    Submodule.map (mapRedDist d) (locallyZeroRedDist L) =
      physicalNonfaceCubeSpan facets d := by
  rw [locallyZeroRedDist_eq_reducedCoordinateCommonRestrictionKernel
    facets L hprimitive]
  exact
    map_reducedCoordinateCommonRestrictionKernel_eq_physicalNonfaceCubeSpan
      facets d hd

end FacetRestrictionData

end GeneralSphereT.PathAlgebra

namespace GeneralSphereT.SimplicialCochain

open GeneralSphereT.PathAlgebra
open GeneralSphereT.PathAlgebra.FacetRestrictionData

variable {V G : Type*} [LinearOrder V] [Fintype V] [AddCommGroup G]
variable (K : AbstractSimplicialComplex V)

/-- The ambient vertex order induces the coordinate order used by the cube
description of the distribution identity subgroup. -/
local instance section4SimplexColexOrder (n : ℕ) : LinearOrder (Simplex K n) :=
  LinearOrder.lift'
    (fun η : Simplex K n => toColex η.1)
    ((toColex : Finset V ≃ Colex (Finset V)).injective.comp
      Subtype.val_injective)

/-- In the concrete simplicial cochain model, abstract local vanishing is
literally the common kernel of all simplex coordinate restrictions. -/
theorem simplicialLocallyZeroRedDist_eq_commonKernel (n : ℕ) :
    locallyZeroRedDist (facetRestrictionData (G := G) K n) =
      reducedCoordinateCommonRestrictionKernel (G := G)
        (fun σ : NonemptySimplex K => facesIn K n σ) := by
  exact
    locallyZeroRedDist_eq_reducedCoordinateCommonRestrictionKernel
      (fun σ : NonemptySimplex K => facesIn K n σ)
      (facetRestrictionData (G := G) K n)
      (facetRestrictionData_primitiveRes (G := G) K n)

/-- The concrete denominator image equality needed by the degree-zero row. -/
theorem simplicialMapLocallyZero_eq_physicalNonfaceCubeSpan (n : ℕ) :
    Submodule.map (mapRedDist (coboundaryToRange (G := G) K n))
        (locallyZeroRedDist (facetRestrictionData (G := G) K n)) =
      physicalNonfaceCubeSpan
        (fun σ : NonemptySimplex K => facesIn K n σ)
        (coboundaryToRange (G := G) K n) := by
  exact
    map_locallyZeroRedDist_eq_physicalNonfaceCubeSpan
      (fun σ : NonemptySimplex K => facesIn K n σ)
      (facetRestrictionData (G := G) K n)
      (facetRestrictionData_primitiveRes (G := G) K n)
      (facetCoboundary_surjective (G := G) K n)

/-- Physical pushforward on reduced distributions is surjective in every
cochain degree. -/
theorem simplicialMapRedDist_surjective (n : ℕ) :
    Function.Surjective
      (mapRedDist (coboundaryToRange (G := G) K n)) :=
  mapRedDist_surjective_of_surjective
    (coboundaryToRange (G := G) K n)
    (facetCoboundary_surjective (G := G) K n)

end GeneralSphereT.SimplicialCochain
