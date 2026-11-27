import Formalization.PrimitiveToPhysicalQuotient
import Formalization.ClosedPrimitiveIdentityImage

set_option linter.style.header false

/-!
# The reverse comparison map under an explicit relative-lift hypothesis

The genuinely simplicial input of (2.34) is isolated in
`PhysicalRelativeLiftData`.  It is a *linear* lift of physical invariant paths
to primitive paths, with the three pointwise properties used in the paper.
Nothing in this file pretends to construct that lift from abstract groups.

Surjectivity of `d` is used only to identify the physical identity denominator
with images of closed primitive words.  Coordinate restriction and facet
coverage enter only when comparing this map with the already constructed
forward map.
-/

noncomputable section

namespace GeneralSphereT.PathAlgebra

open FacetRestrictionData

universe uF uB uBA

variable {ι G : Type*} [LinearOrder ι] [AddCommGroup G]
variable {B : Type uB} [AddCommGroup B]
variable {Facet : Type uF} (facets : Facet → Set ι)
variable {BAt : Facet → Type uBA} [∀ ρ, AddCommGroup (BAt ρ)]
variable {d : Configuration ι G →+ B}

variable (L : FacetRestrictionData
  (CAt := fun ρ => Configuration (facets ρ) G)
  (BAt := BAt) (Facet := Facet) d)

/--
The exact relative primitive-lift input required by (2.34).

In the simplicial application this is the coefficientwise lift supplied by
the relative cochain argument, including the degree-zero constant correction.
Here it is deliberately an explicit hypothesis.
-/
structure PhysicalRelativeLiftData where
  lift : physicalInvariantPaths L →ₗ[ℤ]
    Path (Configuration ι G) (Configuration ι G)
  mapDPath_lift : ∀ e : physicalInvariantPaths L,
    mapDPath d (lift e) =
      (e : Path (Configuration ι G) B)
  lift_mem_elementary : ∀ e : physicalInvariantPaths L,
    lift e ∈ elementaryPaths
      (ι := ι) (G := G) (X := Configuration ι G)
  lift_mem_locallyZero : ∀ e : physicalInvariantPaths L,
    lift e ∈ L.locallyZeroPrimitivePath

namespace PhysicalRelativeLiftData

variable (A : PhysicalRelativeLiftData facets L)

omit [LinearOrder ι] in
/-- Primitive boundary preserves facetwise local vanishing for arbitrary
facet restriction data; no coordinate-order hypothesis is needed here. -/
theorem primitiveReducedBoundary_mem_locallyZeroRedDist
    {R : Path (Configuration ι G) (Configuration ι G)}
    (hR : R ∈ L.locallyZeroPrimitivePath) :
    primitiveReducedBoundary (Configuration ι G) R ∈
      L.locallyZeroRedDist := by
  rw [FacetRestrictionData.locallyZeroRedDist, Submodule.mem_iInf]
  intro ρ
  rw [LinearMap.mem_ker]
  have hRρ : L.restrictPrimitivePath ρ R = 0 :=
    LinearMap.mem_ker.mp
      ((Submodule.mem_iInf (fun σ : Facet =>
        LinearMap.ker (L.restrictPrimitivePath σ))).1 hR ρ)
  calc
    L.restrictRedDist ρ
        (primitiveReducedBoundary (Configuration ι G) R) =
      primitiveReducedBoundary (Configuration (facets ρ) G)
        (L.restrictPrimitivePath ρ R) :=
      LinearMap.congr_fun
        (L.restrictRedDist_primitiveReducedBoundary ρ) R
    _ = 0 := by simp [hRρ]

/-- The reduced primitive boundary of the chosen relative lift. -/
def liftBoundary :
    physicalInvariantPaths L →ₗ[ℤ] RedDist (Configuration ι G) :=
  (primitiveReducedBoundary (Configuration ι G)).comp A.lift

omit [LinearOrder ι] in
/-- The lift boundary of a physical invariant path is a primitive cycle. -/
theorem liftBoundary_mem_Zprim (e : physicalInvariantPaths L) :
    liftBoundary facets L A e ∈ Zprim L := by
  refine ⟨?_, ?_⟩
  · change mapRedDist d
      (primitiveReducedBoundary (Configuration ι G) (A.lift e)) = 0
    calc
      mapRedDist d
          (primitiveReducedBoundary (Configuration ι G) (A.lift e)) =
        configurationReducedBoundary d (mapDPath d (A.lift e)) :=
          LinearMap.congr_fun (mapRedDist_primitiveReducedBoundary d)
            (A.lift e)
      _ = configurationReducedBoundary d
          (e : Path (Configuration ι G) B) := by
            rw [A.mapDPath_lift]
      _ = 0 := LinearMap.mem_ker.mp e.property.2.1
  · exact primitiveReducedBoundary_mem_locallyZeroRedDist facets L
      (A.lift_mem_locallyZero e)

/-- Numerator map for (2.34), with its primitive-cycle codomain recorded. -/
def physicalToPrimitiveCycle :
    physicalInvariantPaths L →ₗ[ℤ] Zprim L :=
  LinearMap.codRestrict (Zprim L) (liftBoundary facets L A)
    (liftBoundary_mem_Zprim facets L A)

omit [LinearOrder ι] in
@[simp]
theorem physicalToPrimitiveCycle_coe (e : physicalInvariantPaths L) :
    (((physicalToPrimitiveCycle facets L A) e : Zprim L) :
      RedDist (Configuration ι G)) =
      primitiveReducedBoundary (Configuration ι G) (A.lift e) :=
  rfl

omit [LinearOrder ι] in
/-- Physical identities are sent into the primitive boundary denominator.
Surjectivity is used only through the easy inclusion in (2.26). -/
theorem physicalIdentityPathsInInvariant_le_comap_physicalToPrimitiveCycle
    (hd : Function.Surjective d) :
    physicalIdentityPathsInInvariantPaths L ≤
      (BprimInZprim L).comap (physicalToPrimitiveCycle facets L A) := by
  intro e he
  change (e : Path (Configuration ι G) B) ∈ physicalIdentityPaths L at he
  have himage := physicalIdentityPaths_le_mapDPath_closedPrimitive L hd he
  rcases himage with ⟨W, hW, hmapW⟩
  have hWclosed :
      primitiveReducedBoundary (Configuration ι G) W = 0 :=
    LinearMap.mem_ker.mp hW.2.1
  let R : Path (Configuration ι G) (Configuration ι G) := A.lift e - W
  have hRmap : mapDPath d R = 0 := by
    change mapDPath d (A.lift e - W) = 0
    rw [map_sub, A.mapDPath_lift, hmapW]
    exact sub_self _
  have hRlocal : R ∈ L.locallyZeroPrimitivePath :=
    L.locallyZeroPrimitivePath.sub_mem
      (A.lift_mem_locallyZero e) hW.2.2
  have hRrelation : R ∈ relationPaths L := by
    rw [relationPaths_eq L]
    exact ⟨LinearMap.mem_ker.mpr hRmap, hRlocal⟩
  change primitiveReducedBoundary (Configuration ι G) (A.lift e) ∈ Bprim L
  rw [Bprim]
  refine ⟨R, hRrelation, ?_⟩
  change primitiveReducedBoundary (Configuration ι G) R =
    primitiveReducedBoundary (Configuration ι G) (A.lift e)
  simp [R, hWclosed]

/-- The reverse comparison map (2.34) on the strict quotients. -/
def physicalToPrimitiveQuotient
    (hd : Function.Surjective d) :
    PhysicalQuotient L →ₗ[ℤ] TPrime L :=
  (physicalIdentityPathsInInvariantPaths L).mapQ
    (BprimInZprim L) (physicalToPrimitiveCycle facets L A)
    (physicalIdentityPathsInInvariant_le_comap_physicalToPrimitiveCycle
      facets L A hd)

omit [LinearOrder ι] in
/-- Representative computation for (2.34). -/
@[simp]
theorem physicalToPrimitiveQuotient_mkQ
    (hd : Function.Surjective d) (e : physicalInvariantPaths L) :
    physicalToPrimitiveQuotient facets L A hd
        ((physicalIdentityPathsInInvariantPaths L).mkQ e) =
      (BprimInZprim L).mkQ (physicalToPrimitiveCycle facets L A e) := by
  simpa only [physicalToPrimitiveQuotient, Submodule.mkQ_apply] using
    (Submodule.mapQ_apply
      (p := physicalIdentityPathsInInvariantPaths L)
      (q := BprimInZprim L) (physicalToPrimitiveCycle facets L A) e)

/-! ## The two comparison maps are inverse -/

/-- Before passing to the primitive quotient, reverse-after-forward differs
from the original primitive cycle by the boundary of the relation path
`A.lift (d_* p_*(s)) - p_*(s)`. -/
theorem physicalToPrimitiveCycle_primitiveToPhysicalInvariant_sub_mem_Bprim
    (hprimitive : ∀ ρ : Facet,
      L.primitiveRes ρ = coordinateRestriction (facets ρ))
    (s : Zprim L) :
    (((physicalToPrimitiveCycle facets L A)
          (primitiveToPhysicalInvariant facets L hprimitive s) : Zprim L) :
        RedDist (Configuration ι G)) -
      (s : RedDist (Configuration ι G)) ∈ Bprim L := by
  let e : physicalInvariantPaths L :=
    primitiveToPhysicalInvariant facets L hprimitive s
  let V : Path (Configuration ι G) (Configuration ι G) :=
    A.lift e - canonicalPath (s : RedDist (Configuration ι G))
  have hVmap : mapDPath d V = 0 := by
    change mapDPath d
      (A.lift e - canonicalPath (s : RedDist (Configuration ι G))) = 0
    rw [map_sub, A.mapDPath_lift]
    change
      (((e : physicalInvariantPaths L) :
          Path (Configuration ι G) B)) -
        mapDPath d (canonicalPath (s : RedDist (Configuration ι G))) = 0
    change mapDPath d (canonicalPath (s : RedDist (Configuration ι G))) -
        mapDPath d (canonicalPath (s : RedDist (Configuration ι G))) = 0
    exact sub_self _
  have hVlocal : V ∈ L.locallyZeroPrimitivePath := by
    apply L.locallyZeroPrimitivePath.sub_mem
    · exact A.lift_mem_locallyZero e
    · exact canonicalPath_mem_locallyZeroPrimitivePath facets L hprimitive
        s.property.2
  have hVrelation : V ∈ relationPaths L := by
    rw [relationPaths_eq L]
    exact ⟨LinearMap.mem_ker.mpr hVmap, hVlocal⟩
  change
    primitiveReducedBoundary (Configuration ι G) (A.lift e) -
      (s : RedDist (Configuration ι G)) ∈ Bprim L
  rw [Bprim]
  refine ⟨V, hVrelation, ?_⟩
  change primitiveReducedBoundary (Configuration ι G)
      (A.lift e - canonicalPath (s : RedDist (Configuration ι G))) =
    primitiveReducedBoundary (Configuration ι G) (A.lift e) -
      (s : RedDist (Configuration ι G))
  rw [map_sub]
  have hcanonical := LinearMap.congr_fun
    primitiveReducedBoundary_canonicalPath
      (s : RedDist (Configuration ι G))
  change primitiveReducedBoundary (Configuration ι G)
      (canonicalPath (s : RedDist (Configuration ι G))) =
    (s : RedDist (Configuration ι G)) at hcanonical
  rw [hcanonical]

/-- Before passing to the physical quotient, forward-after-reverse differs
from the original physical invariant by the image of the closed elementary
locally-zero primitive path `p_*(∂ A.lift(e)) - A.lift(e)`. -/
theorem primitiveToPhysicalInvariant_physicalToPrimitiveCycle_sub_mem_identity
    (hprimitive : ∀ ρ : Facet,
      L.primitiveRes ρ = coordinateRestriction (facets ρ))
    (hcover : ∀ i : ι, ∃ ρ : Facet, i ∈ facets ρ)
    (e : physicalInvariantPaths L) :
    (((primitiveToPhysicalInvariant facets L hprimitive
          (physicalToPrimitiveCycle facets L A e) :
        physicalInvariantPaths L) : Path (Configuration ι G) B)) -
      (e : Path (Configuration ι G) B) ∈ physicalIdentityPaths L := by
  let u : RedDist (Configuration ι G) :=
    primitiveReducedBoundary (Configuration ι G) (A.lift e)
  let V : Path (Configuration ι G) (Configuration ι G) :=
    canonicalPath u - A.lift e
  have hVelem : V ∈ elementaryPaths
      (ι := ι) (G := G) (X := Configuration ι G) := by
    apply (elementaryPaths
      (ι := ι) (G := G) (X := Configuration ι G)).sub_mem
    · exact canonicalPath_mem u
    · exact A.lift_mem_elementary e
  have hVclosed :
      primitiveReducedBoundary (Configuration ι G) V = 0 := by
    change primitiveReducedBoundary (Configuration ι G)
      (canonicalPath u - A.lift e) = 0
    rw [map_sub]
    have hcanonical := LinearMap.congr_fun
      primitiveReducedBoundary_canonicalPath u
    change primitiveReducedBoundary (Configuration ι G)
      (canonicalPath u) = u at hcanonical
    rw [hcanonical]
    exact sub_self _
  have hulocal : u ∈ L.locallyZeroRedDist := by
    exact primitiveReducedBoundary_mem_locallyZeroRedDist facets L
      (A.lift_mem_locallyZero e)
  have hVlocal : V ∈ L.locallyZeroPrimitivePath := by
    apply L.locallyZeroPrimitivePath.sub_mem
    · exact canonicalPath_mem_locallyZeroPrimitivePath facets L hprimitive
        hulocal
    · exact A.lift_mem_locallyZero e
  have hidentity : mapDPath d V ∈ physicalIdentityPaths L :=
    mapDPath_mem_physicalIdentityPaths_of_closed_elementary_locallyZero
      facets L hprimitive hcover hVelem hVclosed hVlocal
  have hmapV :
      mapDPath d V =
        (((primitiveToPhysicalInvariant facets L hprimitive
              (physicalToPrimitiveCycle facets L A e) :
            physicalInvariantPaths L) : Path (Configuration ι G) B)) -
          (e : Path (Configuration ι G) B) := by
    change mapDPath d (canonicalPath u - A.lift e) =
      mapDPath d (canonicalPath u) -
        (e : Path (Configuration ι G) B)
    rw [map_sub, A.mapDPath_lift]
  rw [← hmapV]
  exact hidentity

/-- On `TPrime`, the reverse comparison followed by the forward comparison
is the identity. -/
theorem physicalToPrimitiveQuotient_comp_primitiveToPhysicalQuotient
    (hd : Function.Surjective d)
    (hprimitive : ∀ ρ : Facet,
      L.primitiveRes ρ = coordinateRestriction (facets ρ))
    (hcover : ∀ i : ι, ∃ ρ : Facet, i ∈ facets ρ) :
    (physicalToPrimitiveQuotient facets L A hd).comp
        (primitiveToPhysicalQuotient facets L hprimitive hcover) =
      LinearMap.id := by
  apply LinearMap.ext
  intro q
  refine Submodule.Quotient.induction_on (p := BprimInZprim L) q ?_
  intro s
  change
    physicalToPrimitiveQuotient facets L A hd
        (primitiveToPhysicalQuotient facets L hprimitive hcover
          ((BprimInZprim L).mkQ s)) =
      (BprimInZprim L).mkQ s
  rw [primitiveToPhysicalQuotient_mkQ,
    physicalToPrimitiveQuotient_mkQ]
  apply (Submodule.Quotient.eq (BprimInZprim L)).2
  change
    (((physicalToPrimitiveCycle facets L A
          (primitiveToPhysicalInvariant facets L hprimitive s) - s :
        Zprim L) : RedDist (Configuration ι G))) ∈ Bprim L
  exact physicalToPrimitiveCycle_primitiveToPhysicalInvariant_sub_mem_Bprim
    facets L A hprimitive s

/-- On the physical quotient, the forward comparison followed by the reverse
comparison is the identity. -/
theorem primitiveToPhysicalQuotient_comp_physicalToPrimitiveQuotient
    (hd : Function.Surjective d)
    (hprimitive : ∀ ρ : Facet,
      L.primitiveRes ρ = coordinateRestriction (facets ρ))
    (hcover : ∀ i : ι, ∃ ρ : Facet, i ∈ facets ρ) :
    (primitiveToPhysicalQuotient facets L hprimitive hcover).comp
        (physicalToPrimitiveQuotient facets L A hd) =
      LinearMap.id := by
  apply LinearMap.ext
  intro q
  refine Submodule.Quotient.induction_on
    (p := physicalIdentityPathsInInvariantPaths L) q ?_
  intro e
  change
    primitiveToPhysicalQuotient facets L hprimitive hcover
        (physicalToPrimitiveQuotient facets L A hd
          ((physicalIdentityPathsInInvariantPaths L).mkQ e)) =
      (physicalIdentityPathsInInvariantPaths L).mkQ e
  rw [physicalToPrimitiveQuotient_mkQ,
    primitiveToPhysicalQuotient_mkQ]
  apply (Submodule.Quotient.eq
    (physicalIdentityPathsInInvariantPaths L)).2
  change
    (((primitiveToPhysicalInvariant facets L hprimitive
          (physicalToPrimitiveCycle facets L A e) - e :
        physicalInvariantPaths L) : Path (Configuration ι G) B)) ∈
      physicalIdentityPaths L
  exact
    primitiveToPhysicalInvariant_physicalToPrimitiveCycle_sub_mem_identity
      facets L A hprimitive hcover e

/-- The strict physical and primitive quotients are linearly equivalent once
the explicit relative lift is supplied.  The direction matches (2.34). -/
def physicalPrimitiveLinearEquiv
    (hd : Function.Surjective d)
    (hprimitive : ∀ ρ : Facet,
      L.primitiveRes ρ = coordinateRestriction (facets ρ))
    (hcover : ∀ i : ι, ∃ ρ : Facet, i ∈ facets ρ) :
    PhysicalQuotient L ≃ₗ[ℤ] TPrime L :=
  LinearEquiv.ofLinearMap
    (physicalToPrimitiveQuotient facets L A hd)
    (primitiveToPhysicalQuotient facets L hprimitive hcover)
    (physicalToPrimitiveQuotient_comp_primitiveToPhysicalQuotient
      facets L A hd hprimitive hcover)
    (primitiveToPhysicalQuotient_comp_physicalToPrimitiveQuotient
      facets L A hd hprimitive hcover)

/-! ## Independence of the relative-lift choice -/

omit [LinearOrder ι] in
/-- The pointwise difference of two admissible relative lifts is a relation
path: its physical image vanishes, and it remains facetwise locally zero. -/
theorem lift_sub_lift_mem_relationPaths
    (A₁ A₂ : PhysicalRelativeLiftData facets L)
    (e : physicalInvariantPaths L) :
    A₁.lift e - A₂.lift e ∈ relationPaths L := by
  rw [relationPaths_eq L]
  refine ⟨?_, ?_⟩
  · change mapDPath d (A₁.lift e - A₂.lift e) = 0
    rw [map_sub, A₁.mapDPath_lift, A₂.mapDPath_lift]
    exact sub_self _
  · exact L.locallyZeroPrimitivePath.sub_mem
      (A₁.lift_mem_locallyZero e) (A₂.lift_mem_locallyZero e)

omit [LinearOrder ι] in
/-- Consequently, the two lift-boundary numerator maps differ pointwise by
an element of the primitive boundary denominator. -/
theorem physicalToPrimitiveCycle_sub_mem_Bprim
    (A₁ A₂ : PhysicalRelativeLiftData facets L)
    (e : physicalInvariantPaths L) :
    (((physicalToPrimitiveCycle facets L A₁ e -
          physicalToPrimitiveCycle facets L A₂ e : Zprim L) :
        RedDist (Configuration ι G))) ∈ Bprim L := by
  change
    primitiveReducedBoundary (Configuration ι G) (A₁.lift e) -
      primitiveReducedBoundary (Configuration ι G) (A₂.lift e) ∈ Bprim L
  rw [← map_sub, Bprim]
  exact ⟨A₁.lift e - A₂.lift e,
    lift_sub_lift_mem_relationPaths facets L A₁ A₂ e, rfl⟩

omit [LinearOrder ι] in
/-- The reverse comparison map is canonical: any two admissible linear
relative lifts induce exactly the same map on the physical quotient. -/
theorem physicalToPrimitiveQuotient_independent_of_lift
    (A₁ A₂ : PhysicalRelativeLiftData facets L)
    (hd : Function.Surjective d) :
    physicalToPrimitiveQuotient facets L A₁ hd =
      physicalToPrimitiveQuotient facets L A₂ hd := by
  apply LinearMap.ext
  intro q
  refine Submodule.Quotient.induction_on
    (p := physicalIdentityPathsInInvariantPaths L) q ?_
  intro e
  change
    physicalToPrimitiveQuotient facets L A₁ hd
        ((physicalIdentityPathsInInvariantPaths L).mkQ e) =
      physicalToPrimitiveQuotient facets L A₂ hd
        ((physicalIdentityPathsInInvariantPaths L).mkQ e)
  rw [physicalToPrimitiveQuotient_mkQ,
    physicalToPrimitiveQuotient_mkQ]
  apply (Submodule.Quotient.eq (BprimInZprim L)).2
  change
    (((physicalToPrimitiveCycle facets L A₁ e -
          physicalToPrimitiveCycle facets L A₂ e : Zprim L) :
        RedDist (Configuration ι G))) ∈ Bprim L
  exact physicalToPrimitiveCycle_sub_mem_Bprim facets L A₁ A₂ e

/-- The resulting comparison equivalence is independent of the admissible
relative lift used to construct its reverse direction. -/
theorem physicalPrimitiveLinearEquiv_independent_of_lift
    (A₁ A₂ : PhysicalRelativeLiftData facets L)
    (hd : Function.Surjective d)
    (hprimitive : ∀ ρ : Facet,
      L.primitiveRes ρ = coordinateRestriction (facets ρ))
    (hcover : ∀ i : ι, ∃ ρ : Facet, i ∈ facets ρ) :
    physicalPrimitiveLinearEquiv facets L A₁ hd hprimitive hcover =
      physicalPrimitiveLinearEquiv facets L A₂ hd hprimitive hcover := by
  apply LinearEquiv.ext
  intro q
  change physicalToPrimitiveQuotient facets L A₁ hd q =
    physicalToPrimitiveQuotient facets L A₂ hd q
  exact LinearMap.congr_fun
    (physicalToPrimitiveQuotient_independent_of_lift
      facets L A₁ A₂ hd) q

end PhysicalRelativeLiftData

end GeneralSphereT.PathAlgebra
