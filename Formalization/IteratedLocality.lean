import Formalization.PhysicalQuotientCore

set_option linter.style.header false

/-!
# Iterated physical locality identities

This module upgrades the `k = 0` square core to the full family from
(2.3)--(2.4).  A list records the transverse increments in
`(T_{d r_1} - 1) ... (T_{d r_k} - 1)`.  The no-common-facet condition is put
on the single concatenated list `s :: t :: rs`; consequently the local-zero
proof is a direct split according to which member of that list vanishes.
-/

noncomputable section

namespace GeneralSphereT.PathAlgebra

universe uF uI uJ uX uY uC uB

section IteratedDifferences

variable {I X : Type*} [AddCommGroup I] [AddCommGroup X]

/-- Repeated base differences `(T_{φ r} - 1)`, in the order carried by a list. -/
def iteratedBaseDifference (φ : I →+ X) :
    List I → Path I X →ₗ[ℤ] Path I X
  | [] => LinearMap.id
  | r :: rs =>
      (iteratedBaseDifference φ rs).comp (baseDifference (φ r))

@[simp]
theorem iteratedBaseDifference_nil (φ : I →+ X) (p : Path I X) :
    iteratedBaseDifference φ [] p = p :=
  rfl

@[simp]
theorem iteratedBaseDifference_cons
    (φ : I →+ X) (r : I) (rs : List I) (p : Path I X) :
    iteratedBaseDifference φ (r :: rs) p =
      iteratedBaseDifference φ rs (baseDifference (φ r) p) :=
  rfl

@[simp]
theorem baseDifference_zero :
    baseDifference (0 : X) = (0 : Path I X →ₗ[ℤ] Path I X) := by
  ext p
  change baseDifference (0 : X) (edge p.1 p.2) = 0
  simp [baseDifference]

/-- Pushing a path forward commutes with translating all of its base points. -/
theorem mapPath_baseTranslation
    {J Y : Type*} [AddCommGroup J] [AddCommGroup Y]
    (i : I →+ J) (b : X →+ Y) (u : X) :
    (mapPath i b).comp (baseTranslation u) =
      (baseTranslation (b u)).comp (mapPath i b) := by
  ext p
  change mapPath i b (baseTranslation u (edge p.1 p.2)) =
    baseTranslation (b u) (mapPath i b (edge p.1 p.2))
  simp

/-- Pushing a path forward commutes with one base-difference operator. -/
theorem mapPath_baseDifference
    {J Y : Type*} [AddCommGroup J] [AddCommGroup Y]
    (i : I →+ J) (b : X →+ Y) (u : X) :
    (mapPath i b).comp (baseDifference u) =
      (baseDifference (b u)).comp (mapPath i b) := by
  ext p
  change mapPath i b (baseDifference u (edge p.1 p.2)) =
    baseDifference (b u) (mapPath i b (edge p.1 p.2))
  simp [baseDifference]

/-- Naturality of all repeated differences under a commuting square. -/
theorem mapPath_iteratedBaseDifference_apply
    {J Y : Type*} [AddCommGroup J] [AddCommGroup Y]
    (φ : I →+ X) (ψ : J →+ Y)
    (i : I →+ J) (b : X →+ Y)
    (h : b.comp φ = ψ.comp i)
    (rs : List I) (p : Path I X) :
    mapPath i b (iteratedBaseDifference φ rs p) =
      iteratedBaseDifference ψ (rs.map i) (mapPath i b p) := by
  induction rs generalizing p with
  | nil => simp
  | cons r rs ih =>
      simp only [iteratedBaseDifference_cons, List.map_cons]
      rw [ih]
      have hdifference :
          mapPath i b (baseDifference (φ r) p) =
            baseDifference (b (φ r)) (mapPath i b p) :=
        LinearMap.congr_fun (mapPath_baseDifference i b (φ r)) p
      rw [hdifference]
      have hrmap : b (φ r) = ψ (i r) := by
        simpa using DFunLike.congr_fun h r
      rw [hrmap]

/-- Linear-map form of naturality for all repeated differences. -/
theorem mapPath_iteratedBaseDifference
    {J Y : Type*} [AddCommGroup J] [AddCommGroup Y]
    (φ : I →+ X) (ψ : J →+ Y)
    (i : I →+ J) (b : X →+ Y)
    (h : b.comp φ = ψ.comp i) (rs : List I) :
    (mapPath i b).comp (iteratedBaseDifference φ rs) =
      (iteratedBaseDifference ψ (rs.map i)).comp (mapPath i b) := by
  apply LinearMap.ext
  intro p
  exact mapPath_iteratedBaseDifference_apply φ ψ i b h rs p

/-- If one listed increment has zero displacement, the whole product vanishes. -/
theorem iteratedBaseDifference_eq_zero_of_mem_ker
    (φ : I →+ X) (rs : List I) (p : Path I X)
    {r : I} (hr : r ∈ rs) (hφ : φ r = 0) :
    iteratedBaseDifference φ rs p = 0 := by
  induction rs generalizing p with
  | nil => simp at hr
  | cons u rs ih =>
      simp only [List.mem_cons] at hr
      rcases hr with rfl | hr
      · simp [hφ]
      · exact ih (baseDifference (φ u) p) hr

/-- Translating a square only translates its base. -/
theorem baseTranslation_square
    (φ : I →+ X) (u : X) (s t : I) (x : X) :
    baseTranslation u (square φ s t x) =
      square φ s t (x + u) := by
  simp [square, add_assoc, add_comm]

/-- One difference of a square is the difference of two squares. -/
theorem baseDifference_square
    (φ : I →+ X) (r s t : I) (x : X) :
    baseDifference (φ r) (square φ s t x) =
      square φ s t (x + φ r) - square φ s t x := by
  simp [baseDifference, baseTranslation_square]

/-- Every iterated difference of a square is still a boundary-zero path. -/
@[simp]
theorem boundary_iteratedBaseDifference_square
    (φ : I →+ X) (rs : List I) (s t : I) (x : X) :
    boundary φ (iteratedBaseDifference φ rs (square φ s t x)) = 0 := by
  induction rs generalizing x with
  | nil => simp
  | cons r rs ih =>
      rw [iteratedBaseDifference_cons, baseDifference_square]
      simp only [map_sub, ih, sub_self]

end IteratedDifferences

section ListFacetCondition

variable {Facet : Type uF} {I : Type uI} [AddCommGroup I]
variable {IAt : Facet → Type*} [∀ ρ, AddCommGroup (IAt ρ)]

/--
No facet sees every member of a list.  This is exactly `NoCommonFacet` for
the list's canonical `Fin length` indexing, so repetitions are retained.
-/
def NoCommonFacetList (res : ∀ ρ : Facet, I →+ IAt ρ)
    (increments : List I) : Prop :=
  NoCommonFacet res increments.get

/-- Membership form of the list-indexed no-common-facet condition. -/
theorem noCommonFacetList_iff
    (res : ∀ ρ : Facet, I →+ IAt ρ) (increments : List I) :
    NoCommonFacetList res increments ↔
      ∀ ρ : Facet, ∃ r ∈ increments, res ρ r = 0 := by
  unfold NoCommonFacetList NoCommonFacet
  constructor
  · intro h ρ
    exact List.exists_mem_iff_get.mpr (h ρ)
  · intro h ρ
    exact List.exists_mem_iff_get.mp (h ρ)

/-- At `k = 0`, the list condition is the earlier two-increment condition. -/
theorem noCommonFacetList_pair_iff
    (res : ∀ ρ : Facet, I →+ IAt ρ) (s t : I) :
    NoCommonFacetList res [s, t] ↔
      NoCommonFacet res (pairIncrements s t) := by
  rw [noCommonFacetList_iff, noCommonFacet_pair_iff]
  simp

end ListFacetCondition

section PhysicalIteratedLocality

variable {C B : Type*} [AddCommGroup C] [AddCommGroup B]
variable {Facet : Type uF}
variable {CAt : Facet → Type uC} {BAt : Facet → Type uB}
variable [∀ ρ, AddCommGroup (CAt ρ)] [∀ ρ, AddCommGroup (BAt ρ)]
variable {d : C →+ B}

variable (L : FacetRestrictionData
  (CAt := CAt) (BAt := BAt) (Facet := Facet) d)

/-- The paper's full basic locality expression for a chosen finite list. -/
def iteratedPhysicalLocalitySquare
    (d : C →+ B) (s t : C) (rs : List C) (a : B) : Path C B :=
  iteratedBaseDifference d rs (physicalLocalitySquare d s t a)

@[simp]
theorem iteratedPhysicalLocalitySquare_nil
    (d : C →+ B) (s t : C) (a : B) :
    iteratedPhysicalLocalitySquare d s t [] a =
      physicalLocalitySquare d s t a :=
  rfl

/-- Facet restriction commutes with the complete iterated locality expression. -/
theorem restrictPhysicalPath_iteratedPhysicalLocalitySquare
    (ρ : Facet) (s t : C) (rs : List C) (a : B) :
    L.restrictPhysicalPath ρ
        (iteratedPhysicalLocalitySquare d s t rs a) =
      iteratedBaseDifference (L.localD ρ)
        (rs.map (L.primitiveRes ρ))
        (physicalLocalitySquare (L.localD ρ)
          (L.primitiveRes ρ s) (L.primitiveRes ρ t)
          (L.physicalRes ρ a)) := by
  change
    mapPath (L.primitiveRes ρ) (L.physicalRes ρ)
        (iteratedBaseDifference d rs
          (physicalLocalitySquare d s t a)) = _
  rw [mapPath_iteratedBaseDifference_apply d (L.localD ρ)
    (L.primitiveRes ρ) (L.physicalRes ρ) (L.commutes ρ)]
  have hsquare :=
    restrictPhysicalPath_physicalLocalitySquare L ρ s t a
  change
    mapPath (L.primitiveRes ρ) (L.physicalRes ρ)
        (physicalLocalitySquare d s t a) =
      physicalLocalitySquare (L.localD ρ)
        (L.primitiveRes ρ s) (L.primitiveRes ρ t)
        (L.physicalRes ρ a) at hsquare
  rw [hsquare]

/-- Every full basic locality expression is a physical cycle. -/
@[simp]
theorem configurationBoundary_iteratedPhysicalLocalitySquare
    (s t : C) (rs : List C) (a : B) :
    configurationBoundary d
      (iteratedPhysicalLocalitySquare d s t rs a) = 0 := by
  exact boundary_iteratedBaseDifference_square d rs s t a

/--
The concatenated no-common-facet condition makes the full locality expression
vanish after every facet restriction.
-/
theorem iteratedPhysicalLocalitySquare_mem_locallyZeroPhysicalPath
    (s t : C) (rs : List C) (a : B)
    (hst : NoCommonFacetList L.primitiveRes (s :: t :: rs)) :
    iteratedPhysicalLocalitySquare d s t rs a ∈
      L.locallyZeroPhysicalPath := by
  rw [FacetRestrictionData.locallyZeroPhysicalPath, Submodule.mem_iInf]
  intro ρ
  change L.restrictPhysicalPath ρ
    (iteratedPhysicalLocalitySquare d s t rs a) = 0
  rw [restrictPhysicalPath_iteratedPhysicalLocalitySquare L]
  obtain ⟨r, hr, hρ⟩ :=
    (noCommonFacetList_iff L.primitiveRes (s :: t :: rs)).mp hst ρ
  simp only [List.mem_cons] at hr
  rcases hr with rfl | rfl | hr
  · simp [physicalLocalitySquare, hρ]
  · simp [physicalLocalitySquare, hρ]
  · apply iteratedBaseDifference_eq_zero_of_mem_ker
      (r := L.primitiveRes ρ r)
    · exact List.mem_map.mpr ⟨r, hr, rfl⟩
    · simp [hρ]

end PhysicalIteratedLocality

section ElementaryStability

variable {ι G B : Type*}
variable [LinearOrder ι] [AddCommGroup G] [AddCommGroup B]

omit [LinearOrder ι] in
/-- Base translation does not change the active elementary increment. -/
theorem baseTranslation_mem_elementaryPaths
    (u : B) {p : Path (Configuration ι G) B}
    (hp : p ∈ elementaryPaths (ι := ι) (G := G) (X := B)) :
    baseTranslation u p ∈
      elementaryPaths (ι := ι) (G := G) (X := B) := by
  change p ∈ Submodule.span ℤ
    {q | ∃ (i : ι) (g : G) (a : B),
      g ≠ 0 ∧ q = edge (Finsupp.single i g) a} at hp
  induction hp using Submodule.span_induction with
  | mem p hp =>
      rcases hp with ⟨i, g, a, hg, rfl⟩
      rw [baseTranslation_edge]
      exact elementaryEdge_mem i hg (a + u)
  | zero => simp
  | add p q hp hq ihp ihq =>
      simpa using
        (Submodule.add_mem
          (elementaryPaths (ι := ι) (G := G) (X := B)) ihp ihq)
  | smul n p hp ih =>
      simpa using
        (Submodule.smul_mem
          (elementaryPaths (ι := ι) (G := G) (X := B)) n ih)

omit [LinearOrder ι] in
/-- One base difference preserves the elementary path submodule. -/
theorem baseDifference_mem_elementaryPaths
    (u : B) {p : Path (Configuration ι G) B}
    (hp : p ∈ elementaryPaths (ι := ι) (G := G) (X := B)) :
    baseDifference u p ∈
      elementaryPaths (ι := ι) (G := G) (X := B) := by
  change baseTranslation u p - p ∈
    elementaryPaths (ι := ι) (G := G) (X := B)
  exact Submodule.sub_mem _ (baseTranslation_mem_elementaryPaths u hp) hp

omit [LinearOrder ι] in
/-- Every finite product of base differences preserves elementary paths. -/
theorem iteratedBaseDifference_mem_elementaryPaths
    (d : Configuration ι G →+ B) (rs : List (Configuration ι G))
    {p : Path (Configuration ι G) B}
    (hp : p ∈ elementaryPaths (ι := ι) (G := G) (X := B)) :
    iteratedBaseDifference d rs p ∈
      elementaryPaths (ι := ι) (G := G) (X := B) := by
  induction rs generalizing p with
  | nil => simpa using hp
  | cons r rs ih =>
      exact ih (baseDifference_mem_elementaryPaths (d r) hp)

omit [LinearOrder ι] in
/-- Active elementary `s,t` keep the whole iterated square elementary. -/
theorem iteratedPhysicalLocalitySquare_mem_elementaryPaths
    (d : Configuration ι G →+ B)
    (i : ι) {g : G} (hg : g ≠ 0)
    (j : ι) {h : G} (hh : h ≠ 0)
    (rs : List (Configuration ι G)) (a : B) :
    iteratedPhysicalLocalitySquare d
        (Finsupp.single i g) (Finsupp.single j h) rs a ∈
      elementaryPaths (ι := ι) (G := G) (X := B) := by
  apply iteratedBaseDifference_mem_elementaryPaths d rs
  exact elementaryPhysicalLocalitySquare_mem_elementaryPaths
    (d := d) i hg j hh a

end ElementaryStability

section FullPhysicalDenominator

variable {ι G B : Type*}
variable [LinearOrder ι] [AddCommGroup G] [AddCommGroup B]
variable {Facet : Type uF}
variable {CAt : Facet → Type uC} {BAt : Facet → Type uB}
variable [∀ ρ, AddCommGroup (CAt ρ)] [∀ ρ, AddCommGroup (BAt ρ)]
variable {d : Configuration ι G →+ B}

variable (L : FacetRestrictionData
  (CAt := CAt) (BAt := BAt) (Facet := Facet) d)

/-- The complete set of basic locality identities from (2.3)--(2.4). -/
def physicalLocalityIdentityGenerators :
    Set (Path (Configuration ι G) B) :=
  {R | ∃ (i : ι) (g : G) (j : ι) (h : G)
      (rs : List (Configuration ι G)) (a : B),
    g ≠ 0 ∧ h ≠ 0 ∧
      NoCommonFacetList L.primitiveRes
        (Finsupp.single i g :: Finsupp.single j h :: rs) ∧
      R = iteratedPhysicalLocalitySquare d
        (Finsupp.single i g) (Finsupp.single j h) rs a}

/-- The paper's full physical identity submodule `E_id`. -/
def physicalIdentityPaths :
    Submodule ℤ (Path (Configuration ι G) B) :=
  Submodule.span ℤ (physicalLocalityIdentityGenerators L)

omit [LinearOrder ι] in
/-- The old `k = 0` denominator is contained in the full denominator. -/
theorem physicalBasicSquareDenominator_le_physicalIdentityPaths :
    physicalBasicSquareDenominator L ≤ physicalIdentityPaths L := by
  rw [physicalBasicSquareDenominator, physicalIdentityPaths,
    Submodule.span_le]
  rintro R ⟨i, g, j, h, a, hg, hh, hst, rfl⟩
  apply Submodule.subset_span
  refine ⟨i, g, j, h, [], a, hg, hh, ?_, rfl⟩
  exact (noCommonFacetList_pair_iff L.primitiveRes
    (Finsupp.single i g) (Finsupp.single j h)).2 hst

omit [LinearOrder ι] in
/-- Every full locality generator is an elementary path. -/
theorem physicalLocalityIdentityGenerators_subset_elementaryPaths :
    physicalLocalityIdentityGenerators L ⊆
      elementaryPaths (ι := ι) (G := G) (X := B) := by
  rintro R ⟨i, g, j, h, rs, a, hg, hh, hst, rfl⟩
  exact iteratedPhysicalLocalitySquare_mem_elementaryPaths
    d i hg j hh rs a

omit [LinearOrder ι] in
/-- Every full locality generator has reduced physical boundary zero. -/
theorem physicalLocalityIdentityGenerators_subset_reducedBoundaryKer :
    physicalLocalityIdentityGenerators L ⊆
      LinearMap.ker (configurationReducedBoundary d) := by
  rintro R ⟨i, g, j, h, rs, a, hg, hh, hst, rfl⟩
  change configurationReducedBoundary d
      (iteratedPhysicalLocalitySquare d
        (Finsupp.single i g) (Finsupp.single j h) rs a) = 0
  apply Subtype.ext
  exact configurationBoundary_iteratedPhysicalLocalitySquare
    (d := d) (Finsupp.single i g) (Finsupp.single j h) rs a

omit [LinearOrder ι] in
/-- Every full locality generator vanishes after every facet restriction. -/
theorem physicalLocalityIdentityGenerators_subset_locallyZero :
    physicalLocalityIdentityGenerators L ⊆
      L.locallyZeroPhysicalPath := by
  rintro R ⟨i, g, j, h, rs, a, hg, hh, hst, rfl⟩
  exact iteratedPhysicalLocalitySquare_mem_locallyZeroPhysicalPath
    L (Finsupp.single i g) (Finsupp.single j h) rs a hst

omit [LinearOrder ι] in
/-- The full denominator remains inside the elementary path subgroup. -/
theorem physicalIdentityPaths_le_elementaryPaths :
    physicalIdentityPaths L ≤
      elementaryPaths (ι := ι) (G := G) (X := B) := by
  rw [physicalIdentityPaths, Submodule.span_le]
  exact physicalLocalityIdentityGenerators_subset_elementaryPaths L

omit [LinearOrder ι] in
/-- The full denominator consists of reduced physical cycles. -/
theorem physicalIdentityPaths_le_reducedBoundaryKer :
    physicalIdentityPaths L ≤
      LinearMap.ker (configurationReducedBoundary d) := by
  rw [physicalIdentityPaths, Submodule.span_le]
  exact physicalLocalityIdentityGenerators_subset_reducedBoundaryKer L

omit [LinearOrder ι] in
/-- The full denominator is locally zero. -/
theorem physicalIdentityPaths_le_locallyZeroPhysicalPath :
    physicalIdentityPaths L ≤ L.locallyZeroPhysicalPath := by
  rw [physicalIdentityPaths, Submodule.span_le]
  exact physicalLocalityIdentityGenerators_subset_locallyZero L

omit [LinearOrder ι] in
/-- The complete paper denominator `E_id` lies in the exact numerator `E_inv`. -/
theorem physicalIdentityPaths_le_physicalInvariantPaths :
    physicalIdentityPaths L ≤ physicalInvariantPaths L := by
  intro R hR
  exact ⟨physicalIdentityPaths_le_elementaryPaths L hR,
    physicalIdentityPaths_le_reducedBoundaryKer L hR,
    physicalIdentityPaths_le_locallyZeroPhysicalPath L hR⟩

/-- The full denominator regarded as a submodule of `E_inv`. -/
def physicalIdentityPathsInInvariantPaths :
    Submodule ℤ (physicalInvariantPaths L) :=
  Submodule.comap (physicalInvariantPaths L).subtype
    (physicalIdentityPaths L)

/-- The typed physical quotient `T = E_inv / E_id`. -/
abbrev PhysicalQuotient :=
  physicalInvariantPaths L ⧸ physicalIdentityPathsInInvariantPaths L

end FullPhysicalDenominator

end GeneralSphereT.PathAlgebra
