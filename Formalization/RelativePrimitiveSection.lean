import Formalization.PhysicalToPrimitiveQuotient

set_option linter.style.header false

/-!
# Relative primitive sections and the reverse comparison lift

The simplicial argument in (2.22)--(2.24) produces, for every active
coordinate, a set-theoretic section of the coboundary map.  Its restriction to
any facet containing that coordinate is a fixed function of the restricted
physical base.  No additivity of the section is required: extending a function
on basis elements of a free integral path group is automatically linear.

This file packages exactly that data and constructs the
`PhysicalRelativeLiftData` used by the already verified reverse quotient map.
The construction acts directly on elementary edge generators, avoiding a
coefficient-by-coefficient basis choice.
-/

noncomputable section

namespace GeneralSphereT.PathAlgebra

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
Set-theoretic primitive sections adapted to every coordinate and every facet
which sees that coordinate.

The local sections need not be additive.  Their only role is to state that the
restriction of the chosen global primitive depends solely on the restricted
physical configuration.
-/
structure RelativePrimitiveSectionData where
  globalPrimitive : ι → B → Configuration ι G
  map_globalPrimitive : ∀ (i : ι) (a : B), d (globalPrimitive i a) = a
  localPrimitive : ∀ (ρ : Facet), facets ρ → BAt ρ → Configuration (facets ρ) G
  restrict_globalPrimitive : ∀ (ρ : Facet) (i : ι) (hi : i ∈ facets ρ) (a : B),
    coordinateRestriction (facets ρ) (globalPrimitive i a) =
      localPrimitive ρ ⟨i, hi⟩ (L.physicalRes ρ a)

namespace RelativePrimitiveSectionData

variable (A : RelativePrimitiveSectionData facets L)

/-- Lift one raw path generator when its increment has exactly one active
coordinate, and send all other increments to zero. -/
private noncomputable def liftEdgeTerm
    (chooseBase : ι → B → Configuration ι G)
    (r : Configuration ι G) (a : B) :
    Path (Configuration ι G) (Configuration ι G) :=
  if h : r.support.Nonempty ∧ r.support.card = 1 then
    edge r (chooseBase (r.support.min' h.1) a)
  else
    0

omit [AddCommGroup B] in
private theorem liftEdgeTerm_single
    (chooseBase : ι → B → Configuration ι G)
    (i : ι) {g : G} (hg : g ≠ 0) (a : B) :
    liftEdgeTerm chooseBase (Finsupp.single i g) a =
      edge (Finsupp.single i g) (chooseBase i a) := by
  classical
  simp [liftEdgeTerm, hg]

omit [AddCommGroup B] in
private theorem liftEdgeTerm_zero
    (chooseBase : ι → B → Configuration ι G) (a : B) :
    liftEdgeTerm chooseBase 0 a = 0 := by
  classical
  simp [liftEdgeTerm]

/-- Linear extension of the relative lift before quotienting zero increments. -/
def rawRelativeLift :
    RawPath (Configuration ι G) B →ₗ[ℤ]
      Path (Configuration ι G) (Configuration ι G) :=
  Finsupp.linearCombination ℤ fun p =>
    liftEdgeTerm A.globalPrimitive p.1 p.2

@[simp]
theorem rawRelativeLift_rawEdge_single
    (i : ι) {g : G} (hg : g ≠ 0) (a : B) :
    rawRelativeLift facets L A (rawEdge (Finsupp.single i g) a) =
      edge (Finsupp.single i g) (A.globalPrimitive i a) := by
  classical
  simp [rawRelativeLift, rawEdge, liftEdgeTerm_single, hg]

theorem zeroIncrement_le_rawRelativeLift_ker :
    zeroIncrement (Configuration ι G) B ≤
      LinearMap.ker (rawRelativeLift facets L A) := by
  rw [zeroIncrement, Submodule.span_le]
  rintro _ ⟨a, rfl⟩
  change rawRelativeLift facets L A (rawEdge 0 a) = 0
  classical
  simp [rawRelativeLift, rawEdge, liftEdgeTerm_zero]

/-- The global relative lift on the zero-increment path quotient. -/
def relativeLift :
    Path (Configuration ι G) B →ₗ[ℤ]
      Path (Configuration ι G) (Configuration ι G) :=
  (zeroIncrement (Configuration ι G) B).liftQ
    (rawRelativeLift facets L A)
    (zeroIncrement_le_rawRelativeLift_ker facets L A)

@[simp]
theorem relativeLift_edge_single
    (i : ι) {g : G} (hg : g ≠ 0) (a : B) :
    relativeLift facets L A (edge (Finsupp.single i g) a) =
      edge (Finsupp.single i g) (A.globalPrimitive i a) := by
  exact rawRelativeLift_rawEdge_single facets L A i hg a

/-- The same generatorwise construction over one facet. -/
def localRelativeLift (ρ : Facet) :
    Path (Configuration (facets ρ) G) (BAt ρ) →ₗ[ℤ]
      Path (Configuration (facets ρ) G)
        (Configuration (facets ρ) G) :=
  let localData : (facets ρ) → BAt ρ → Configuration (facets ρ) G :=
    A.localPrimitive ρ
  (zeroIncrement (Configuration (facets ρ) G) (BAt ρ)).liftQ
    (Finsupp.linearCombination ℤ fun p =>
      liftEdgeTerm localData p.1 p.2)
    (by
      rw [zeroIncrement, Submodule.span_le]
      rintro _ ⟨a, rfl⟩
      classical
      simp [liftEdgeTerm_zero])

@[simp]
theorem localRelativeLift_edge_single
    (ρ : Facet) (i : facets ρ) {g : G} (hg : g ≠ 0) (a : BAt ρ) :
    localRelativeLift facets L A ρ (edge (Finsupp.single i g) a) =
      edge (Finsupp.single i g) (A.localPrimitive ρ i a) := by
  classical
  simp [localRelativeLift, edge, rawEdge, liftEdgeTerm_single, hg]

/-- On elementary paths the chosen lift is a genuine right inverse to `d_*`. -/
theorem mapDPath_relativeLift_of_mem_elementary
    {p : Path (Configuration ι G) B}
    (hp : p ∈ elementaryPaths (ι := ι) (G := G) (X := B)) :
    mapDPath d (relativeLift facets L A p) = p := by
  change p ∈ Submodule.span ℤ
    {q | ∃ (i : ι) (g : G) (a : B),
      g ≠ 0 ∧ q = edge (Finsupp.single i g) a} at hp
  induction hp using Submodule.span_induction with
  | mem p hp =>
      rcases hp with ⟨i, g, a, hg, rfl⟩
      simp [relativeLift_edge_single, hg, A.map_globalPrimitive]
  | zero => simp
  | add p q _ _ ihp ihq => simp [ihp, ihq]
  | smul n p _ ih => simp [ih]

/-- The relative lift of an elementary physical path is elementary. -/
theorem relativeLift_mem_elementary
    {p : Path (Configuration ι G) B}
    (hp : p ∈ elementaryPaths (ι := ι) (G := G) (X := B)) :
    relativeLift facets L A p ∈
      elementaryPaths (ι := ι) (G := G)
        (X := Configuration ι G) := by
  change p ∈ Submodule.span ℤ
    {q | ∃ (i : ι) (g : G) (a : B),
      g ≠ 0 ∧ q = edge (Finsupp.single i g) a} at hp
  induction hp using Submodule.span_induction with
  | mem p hp =>
      rcases hp with ⟨i, g, a, hg, rfl⟩
      simpa [relativeLift_edge_single, hg] using
        (elementaryEdge_mem (X := Configuration ι G)
          i hg (A.globalPrimitive i a))
  | zero => simp
  | add p q _ _ ihp ihq => simpa using Submodule.add_mem _ ihp ihq
  | smul n p _ ih => simpa using Submodule.smul_mem _ n ih

/-- Relative lifting commutes with restriction on the elementary subgroup. -/
theorem restrictPrimitivePath_relativeLift_of_mem_elementary
    (hprimitive : ∀ ρ : Facet,
      L.primitiveRes ρ = coordinateRestriction (facets ρ))
    {p : Path (Configuration ι G) B}
    (hp : p ∈ elementaryPaths (ι := ι) (G := G) (X := B))
    (ρ : Facet) :
    L.restrictPrimitivePath ρ (relativeLift facets L A p) =
      localRelativeLift facets L A ρ (L.restrictPhysicalPath ρ p) := by
  change p ∈ Submodule.span ℤ
    {q | ∃ (i : ι) (g : G) (a : B),
      g ≠ 0 ∧ q = edge (Finsupp.single i g) a} at hp
  induction hp using Submodule.span_induction with
  | mem p hp =>
      rcases hp with ⟨i, g, a, hg, rfl⟩
      by_cases hi : i ∈ facets ρ
      · rw [relativeLift_edge_single facets L A i hg a]
        simp only [FacetRestrictionData.restrictPrimitivePath,
          FacetRestrictionData.restrictPhysicalPath, mapPath_edge]
        rw [hprimitive ρ]
        rw [coordinateRestriction_single_mem (facets ρ) hi]
        rw [localRelativeLift_edge_single facets L A ρ ⟨i, hi⟩ hg]
        rw [A.restrict_globalPrimitive ρ i hi a]
      · rw [relativeLift_edge_single facets L A i hg a]
        simp only [FacetRestrictionData.restrictPrimitivePath,
          FacetRestrictionData.restrictPhysicalPath, mapPath_edge]
        rw [hprimitive ρ]
        rw [coordinateRestriction_single_not_mem (facets ρ) hi]
        simp
  | zero => simp
  | add p q _ _ ihp ihq => simp [ihp, ihq]
  | smul n p _ ih => simp [ih]

/-- Relative sections give the exact linear path lift required by (2.34). -/
def toPhysicalRelativeLiftData
    (hprimitive : ∀ ρ : Facet,
      L.primitiveRes ρ = coordinateRestriction (facets ρ)) :
    PhysicalRelativeLiftData facets L where
  lift := (relativeLift facets L A).comp (physicalInvariantPaths L).subtype
  mapDPath_lift e :=
    mapDPath_relativeLift_of_mem_elementary facets L A e.property.1
  lift_mem_elementary e :=
    relativeLift_mem_elementary facets L A e.property.1
  lift_mem_locallyZero e := by
    rw [FacetRestrictionData.locallyZeroPrimitivePath,
      Submodule.mem_iInf]
    intro ρ
    change L.restrictPrimitivePath ρ
      (relativeLift facets L A (e : Path (Configuration ι G) B)) = 0
    rw [restrictPrimitivePath_relativeLift_of_mem_elementary
      facets L A hprimitive e.property.1 ρ]
    have hlocal : L.restrictPhysicalPath ρ
        (e : Path (Configuration ι G) B) = 0 :=
      (Submodule.mem_iInf (fun σ : Facet =>
        LinearMap.ker (L.restrictPhysicalPath σ))).1 e.property.2.2 ρ
    simp [hlocal]

end RelativePrimitiveSectionData

end GeneralSphereT.PathAlgebra
