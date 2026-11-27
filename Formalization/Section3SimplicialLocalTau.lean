import Formalization.Section3SimplexLocalTau
import Formalization.SimplicialRelativePrimitiveZero

set_option linter.style.header false

/-!
# Section 3: simplex-local `tau` for simplicial coboundaries

This file supplies the geometric input to `Section3SimplexLocalTau`.  The
carrier is an arbitrary nonempty simplex `ρ`; importantly, it is not assumed
to have the cochain degree.  We normalize a chosen primitive on the closed
star of `ρ`, and then restrict the same cone homotopy to every simplex
containing `ρ`.
-/

noncomputable section

namespace GeneralSphereT.SimplicialCochain

open GeneralSphereT.PathAlgebra
open GeneralSphereT.PathAlgebra.FacetRestrictionData
open GeneralSphereT.PathAlgebra.FacetwisePrimitiveSectionData

variable {V G : Type*} [LinearOrder V] [Fintype V] [AddCommGroup G]
variable (K : AbstractSimplicialComplex V)

/-- The cube-basis proof only needs some ordering of the finite cochain
coordinate type; it is unrelated to the vertex orientation order. -/
local instance simplexCoordinateLinearOrder (n : ℕ) :
    LinearOrder (Simplex K n) := by
  classical
  exact linearOrderOfSTO WellOrderingRel

/-!
## Closed-star normalization for an ungraded carrier simplex
-/

omit [LinearOrder V] [Fintype V] in
/-- A simplex of an abstract simplicial complex is nonempty. -/
theorem carrier_nonempty (ρ : NonemptySimplex K) : ρ.1.Nonempty :=
  (K.isRelLowerSet_faces ρ.2).1

/-- A fixed vertex of the carrier simplex. -/
def carrierApex (ρ : NonemptySimplex K) : V :=
  ρ.1.min' (carrier_nonempty K ρ)

omit [Fintype V] in
@[simp]
theorem carrierApex_mem (ρ : NonemptySimplex K) :
    carrierApex K ρ ∈ ρ.1 :=
  Finset.min'_mem _ _

/-- Degree-`n` cochain coordinates in the closed star of `ρ`. -/
def carrierClosedStarSet (ρ : NonemptySimplex K) (n : ℕ) :
    Set (Simplex K n) :=
  {τ | τ.1 ∪ ρ.1 ∈ K}

/-- Extend a closed-star cochain by zero to the whole complex. -/
def extendCarrierClosedStar (ρ : NonemptySimplex K) (n : ℕ) :
    ClosedStarCochain K ρ n G →+ Cochain K n G :=
  coordinateExtension (carrierClosedStarSet K ρ n)

@[simp]
theorem restrictClosedStar_extendCarrierClosedStar
    (ρ : NonemptySimplex K) (n : ℕ)
    (c : ClosedStarCochain K ρ n G) :
    restrictClosedStar K ρ n (extendCarrierClosedStar K ρ n c) = c := by
  ext τ
  rw [restrictClosedStar_apply]
  change coordinateExtension (carrierClosedStarSet K ρ n) c τ.1 = c τ
  exact coordinateExtension_apply_mem (carrierClosedStarSet K ρ n) c τ.2

/-- Positive-degree primitive normalized on the closed star of `ρ`. -/
def carrierNormalizedPrimitiveSucc (m : ℕ) (ρ : NonemptySimplex K)
    (a : CoboundaryGroup (G := G) K (m + 1)) :
    Cochain K (m + 1) G :=
  let c := chosenPrimitive K (m + 1) a
  let b := coneHomotopy K ρ (carrierApex K ρ) (carrierApex_mem K ρ) m
    (restrictClosedStar K ρ (m + 1) c)
  c - coboundary K m (extendCarrierClosedStar K ρ m b)

@[simp]
theorem coboundary_carrierNormalizedPrimitiveSucc
    (m : ℕ) (ρ : NonemptySimplex K)
    (a : CoboundaryGroup (G := G) K (m + 1)) :
    coboundary K (m + 1) (carrierNormalizedPrimitiveSucc K m ρ a) = a.1 := by
  simp [carrierNormalizedPrimitiveSucc, map_sub]

/-- On the carrier closed star, the normalized positive-degree primitive is
the cone primitive of the physical coboundary. -/
theorem restrictClosedStar_carrierNormalizedPrimitiveSucc
    (m : ℕ) (ρ : NonemptySimplex K)
    (a : CoboundaryGroup (G := G) K (m + 1)) :
    restrictClosedStar K ρ (m + 1)
        (carrierNormalizedPrimitiveSucc K m ρ a) =
      coneHomotopy K ρ (carrierApex K ρ) (carrierApex_mem K ρ)
        (m + 1) (restrictClosedStar K ρ (m + 2) a.1) := by
  let c := chosenPrimitive K (m + 1) a
  let h := coneHomotopy K ρ (carrierApex K ρ) (carrierApex_mem K ρ) m
    (restrictClosedStar K ρ (m + 1) c)
  have hcontract := closedStar_contraction_positive
    (G := G) K ρ (carrierApex K ρ) (carrierApex_mem K ρ) m
      (restrictClosedStar K ρ (m + 1) c)
  have hd :
      closedStarCoboundary K ρ (m + 1)
          (restrictClosedStar K ρ (m + 1) c) =
        restrictClosedStar K ρ (m + 2) a.1 := by
    calc
      _ = restrictClosedStar K ρ (m + 2) (coboundary K (m + 1) c) :=
        (LinearMap.congr_fun
          (restrictClosedStar_coboundary (G := G) K ρ (m + 1)) c).symm
      _ = _ := by simp [c]
  change restrictClosedStar K ρ (m + 1)
      (c - coboundary K m (extendCarrierClosedStar K ρ m h)) = _
  rw [map_sub]
  have hnat := LinearMap.congr_fun
    (restrictClosedStar_coboundary (G := G) K ρ m)
    (extendCarrierClosedStar K ρ m h)
  simp only [LinearMap.comp_apply] at hnat
  rw [hnat, restrictClosedStar_extendCarrierClosedStar]
  nth_rewrite 1 [← hcontract]
  rw [hd]
  abel

/-- Restriction to every simplex containing `ρ` is the corresponding local
cone primitive. -/
theorem restrictFacet_carrierNormalizedPrimitiveSucc
    (m : ℕ) (ρ σ : NonemptySimplex K) (hρσ : ρ.1 ⊆ σ.1)
    (a : CoboundaryGroup (G := G) K (m + 1)) :
    coordinateRestriction (facesIn K (m + 1) σ)
        (carrierNormalizedPrimitiveSucc K m ρ a) =
      simplexConeHomotopy K ρ σ hρσ
        (carrierApex K ρ) (carrierApex_mem K ρ) (m + 1)
        (restrictCoboundary K (m + 1) σ a) := by
  let aStar := restrictClosedStar K ρ (m + 2) a.1
  have hrestrict :
      restrictClosedStarToSimplex K ρ σ hρσ (m + 2) aStar =
        restrictCoboundary K (m + 1) σ a := by
    ext τ
    rfl
  ext τ
  calc
    coordinateRestriction (facesIn K (m + 1) σ)
          (carrierNormalizedPrimitiveSucc K m ρ a) τ =
        restrictClosedStarToSimplex K ρ σ hρσ (m + 1)
          (restrictClosedStar K ρ (m + 1)
            (carrierNormalizedPrimitiveSucc K m ρ a)) τ := by
      rfl
    _ = restrictClosedStarToSimplex K ρ σ hρσ (m + 1)
          (coneHomotopy K ρ (carrierApex K ρ) (carrierApex_mem K ρ)
            (m + 1) aStar) τ := by
      rw [restrictClosedStar_carrierNormalizedPrimitiveSucc]
    _ = simplexConeHomotopy K ρ σ hρσ
          (carrierApex K ρ) (carrierApex_mem K ρ) (m + 1)
          (restrictClosedStarToSimplex K ρ σ hρσ (m + 2) aStar) τ := by
      exact DFunLike.congr_fun
        (LinearMap.congr_fun
          (restrictClosedStarToSimplex_coneHomotopy
            (G := G) K ρ σ hρσ (carrierApex K ρ)
              (carrierApex_mem K ρ) (m + 1)) aStar) τ
    _ = simplexConeHomotopy K ρ σ hρσ
          (carrierApex K ρ) (carrierApex_mem K ρ) (m + 1)
          (restrictCoboundary K (m + 1) σ a) τ := by
      rw [hrestrict]

/-!
## Degree zero
-/

/-- Degree-zero primitive normalized to vanish at the carrier apex. -/
def carrierNormalizedPrimitiveZero (ρ : NonemptySimplex K)
    (a : CoboundaryGroup (G := G) K 0) : Cochain K 0 G :=
  let c := chosenPrimitive K 0 a
  c - constantCochain K
    (closedStarAugmentation K ρ (carrierApex K ρ) (carrierApex_mem K ρ)
      (restrictClosedStar K ρ 0 c))

@[simp]
theorem coboundary_carrierNormalizedPrimitiveZero
    (ρ : NonemptySimplex K) (a : CoboundaryGroup (G := G) K 0) :
    coboundary K 0 (carrierNormalizedPrimitiveZero K ρ a) = a.1 := by
  simp [carrierNormalizedPrimitiveZero]

/-- The normalized degree-zero primitive is the cone primitive on the
carrier closed star. -/
theorem restrictClosedStar_carrierNormalizedPrimitiveZero
    (ρ : NonemptySimplex K) (a : CoboundaryGroup (G := G) K 0) :
    restrictClosedStar K ρ 0 (carrierNormalizedPrimitiveZero K ρ a) =
      coneHomotopy K ρ (carrierApex K ρ) (carrierApex_mem K ρ) 0
        (restrictClosedStar K ρ 1 a.1) := by
  let c := chosenPrimitive K 0 a
  have hcontract := closedStar_contraction_zero
    (G := G) K ρ (carrierApex K ρ) (carrierApex_mem K ρ)
      (restrictClosedStar K ρ 0 c)
  have hd :
      closedStarCoboundary K ρ 0 (restrictClosedStar K ρ 0 c) =
        restrictClosedStar K ρ 1 a.1 := by
    calc
      _ = restrictClosedStar K ρ 1 (coboundary K 0 c) :=
        (LinearMap.congr_fun
          (restrictClosedStar_coboundary (G := G) K ρ 0) c).symm
      _ = _ := by simp [c]
  change restrictClosedStar K ρ 0
      (c - constantCochain K
        (closedStarAugmentation K ρ (carrierApex K ρ)
          (carrierApex_mem K ρ) (restrictClosedStar K ρ 0 c))) = _
  rw [map_sub, restrictClosedStar_constantCochain, ← hd]
  exact hcontract.symm

/-- Degree-zero restriction to every simplex containing the carrier is the
same local cone primitive. -/
theorem restrictFacet_carrierNormalizedPrimitiveZero
    (ρ σ : NonemptySimplex K) (hρσ : ρ.1 ⊆ σ.1)
    (a : CoboundaryGroup (G := G) K 0) :
    coordinateRestriction (facesIn K 0 σ)
        (carrierNormalizedPrimitiveZero K ρ a) =
      simplexConeHomotopy K ρ σ hρσ
        (carrierApex K ρ) (carrierApex_mem K ρ) 0
        (restrictCoboundary K 0 σ a) := by
  let aStar := restrictClosedStar K ρ 1 a.1
  have hrestrict :
      restrictClosedStarToSimplex K ρ σ hρσ 1 aStar =
        restrictCoboundary K 0 σ a := by
    ext τ
    rfl
  ext τ
  calc
    coordinateRestriction (facesIn K 0 σ)
          (carrierNormalizedPrimitiveZero K ρ a) τ =
        restrictClosedStarToSimplex K ρ σ hρσ 0
          (restrictClosedStar K ρ 0
            (carrierNormalizedPrimitiveZero K ρ a)) τ := by
      rfl
    _ = restrictClosedStarToSimplex K ρ σ hρσ 0
          (coneHomotopy K ρ (carrierApex K ρ) (carrierApex_mem K ρ)
            0 aStar) τ := by
      rw [restrictClosedStar_carrierNormalizedPrimitiveZero]
    _ = simplexConeHomotopy K ρ σ hρσ
          (carrierApex K ρ) (carrierApex_mem K ρ) 0
          (restrictClosedStarToSimplex K ρ σ hρσ 1 aStar) τ := by
      exact DFunLike.congr_fun
        (LinearMap.congr_fun
          (restrictClosedStarToSimplex_coneHomotopy
            (G := G) K ρ σ hρσ (carrierApex K ρ)
              (carrierApex_mem K ρ) 0) aStar) τ
    _ = simplexConeHomotopy K ρ σ hρσ
          (carrierApex K ρ) (carrierApex_mem K ρ) 0
          (restrictCoboundary K 0 σ a) τ := by
      rw [hrestrict]

/-!
## The localized facet family and its primitive sections
-/

/-- Simplices in the carrier family: all nonempty simplices containing
`ρ`.  In a finite complex this is equivalent to checking the maximal facets
containing `ρ`, but avoids introducing a separate maximality predicate. -/
abbrev CarrierFacet (ρ : NonemptySimplex K) :=
  {σ : NonemptySimplex K // ρ.1 ⊆ σ.1}

/-- Degree-`n` cochain coordinates seen by a member of the carrier family. -/
def carrierFacetSets (ρ : NonemptySimplex K) (n : ℕ) :
    CarrierFacet K ρ → Set (Simplex K n) :=
  fun σ => facesIn K n σ.1

/-- Facet restriction data restricted to the simplices containing `ρ`. -/
def carrierFacetRestrictionData (ρ : NonemptySimplex K) (n : ℕ) :
    FacetRestrictionData
      (CAt := fun σ : CarrierFacet K ρ =>
        Configuration (carrierFacetSets K ρ n σ) G)
      (BAt := fun σ : CarrierFacet K ρ =>
        Configuration (facesIn K (n + 1) σ.1) G)
      (Facet := CarrierFacet K ρ)
      (coboundaryToRange (G := G) K n) where
  primitiveRes σ := restrictCochain (G := G) K n σ.1
  physicalRes σ := restrictCoboundary (G := G) K n σ.1
  localD σ := (localCoboundary (G := G) K n σ.1).toAddMonoidHom
  commutes σ := by
    apply AddMonoidHom.ext
    intro c
    change restrictCochain (G := G) K (n + 1) σ.1
        (coboundary K n c) =
      localCoboundary K n σ.1 (restrictCochain K n σ.1 c)
    exact DFunLike.congr_fun
      (restrictCochain_coboundary (G := G) K n σ.1) c

@[simp]
theorem carrierFacetRestrictionData_primitiveRes
    (ρ : NonemptySimplex K) (n : ℕ) (σ : CarrierFacet K ρ) :
    (carrierFacetRestrictionData (G := G) K ρ n).primitiveRes σ =
      coordinateRestriction (carrierFacetSets K ρ n σ) :=
  rfl

/-- The positive-degree closed-star normalization, packaged as the exact
set-theoretic section required by the local-`tau` argument. -/
def carrierPrimitiveSectionDataSucc (m : ℕ) (ρ : NonemptySimplex K) :
    FacetwisePrimitiveSectionData
      (carrierFacetRestrictionData (G := G) K ρ (m + 1)) where
  globalPrimitive a := carrierNormalizedPrimitiveSucc K m ρ a
  map_globalPrimitive a := by
    apply Subtype.ext
    exact coboundary_carrierNormalizedPrimitiveSucc K m ρ a
  localPrimitive σ b :=
    simplexConeHomotopy K ρ σ.1 σ.2
      (carrierApex K ρ) (carrierApex_mem K ρ) (m + 1) b
  restrict_globalPrimitive σ a := by
    exact restrictFacet_carrierNormalizedPrimitiveSucc K m ρ σ.1 σ.2 a

/-- The degree-zero closed-star normalization in the same package. -/
def carrierPrimitiveSectionDataZero (ρ : NonemptySimplex K) :
    FacetwisePrimitiveSectionData
      (carrierFacetRestrictionData (G := G) K ρ 0) where
  globalPrimitive a := carrierNormalizedPrimitiveZero K ρ a
  map_globalPrimitive a := by
    apply Subtype.ext
    exact coboundary_carrierNormalizedPrimitiveZero K ρ a
  localPrimitive σ b :=
    simplexConeHomotopy K ρ σ.1 σ.2
      (carrierApex K ρ) (carrierApex_mem K ρ) 0 b
  restrict_globalPrimitive σ a := by
    exact restrictFacet_carrierNormalizedPrimitiveZero K ρ σ.1 σ.2 a

/-!
## Simplex-local `tau` vanishes
-/

/-- Positive-degree refinement used by the cone-operator replacement: every
locally invisible distribution is a sum of local cubes all of whose labels
are elementary. -/
theorem simplexLocalInvariantSucc_le_elementarySpan
    (m : ℕ) (ρ : NonemptySimplex K) :
    FacetRestrictionData.physicalInvariantDistributions
        (carrierFacetRestrictionData (G := G) K ρ (m + 1)) ≤
      elementaryPhysicalNonfaceCubeSpan
        (carrierFacetSets K ρ (m + 1))
        (coboundaryToRange (G := G) K (m + 1)) := by
  exact
    physicalInvariantDistributions_le_elementaryPhysicalNonfaceCubeSpan
      (carrierFacetSets K ρ (m + 1))
      (carrierFacetRestrictionData (G := G) K ρ (m + 1))
      (carrierPrimitiveSectionDataSucc (G := G) K m ρ)
      (carrierFacetRestrictionData_primitiveRes (G := G) K ρ (m + 1))

/-- Degree-zero version of the same elementary decomposition. -/
theorem simplexLocalInvariantZero_le_elementarySpan
    (ρ : NonemptySimplex K) :
    FacetRestrictionData.physicalInvariantDistributions
        (carrierFacetRestrictionData (G := G) K ρ 0) ≤
      elementaryPhysicalNonfaceCubeSpan
        (carrierFacetSets K ρ 0)
        (coboundaryToRange (G := G) K 0) := by
  exact
    physicalInvariantDistributions_le_elementaryPhysicalNonfaceCubeSpan
      (carrierFacetSets K ρ 0)
      (carrierFacetRestrictionData (G := G) K ρ 0)
      (carrierPrimitiveSectionDataZero (G := G) K ρ)
      (carrierFacetRestrictionData_primitiveRes (G := G) K ρ 0)

/-- Uniform elementary-decomposition form in every cochain degree. -/
theorem simplexLocalInvariant_le_elementarySpan
    (n : ℕ) (ρ : NonemptySimplex K) :
    FacetRestrictionData.physicalInvariantDistributions
        (carrierFacetRestrictionData (G := G) K ρ n) ≤
      elementaryPhysicalNonfaceCubeSpan
        (carrierFacetSets K ρ n)
        (coboundaryToRange (G := G) K n) := by
  cases n with
  | zero => exact simplexLocalInvariantZero_le_elementarySpan (G := G) K ρ
  | succ m =>
      simpa [Nat.succ_eq_add_one] using
        simplexLocalInvariantSucc_le_elementarySpan (G := G) K m ρ

/-- Positive cochain degrees: the localized distribution quotient is
trivial. -/
theorem simplexLocalTauSucc_subsingleton
    (m : ℕ) (ρ : NonemptySimplex K) :
    Subsingleton
      (Tau (carrierFacetSets K ρ (m + 1))
        (carrierFacetRestrictionData (G := G) K ρ (m + 1))) := by
  exact GeneralSphereT.PathAlgebra.tau_subsingleton
    (carrierFacetSets K ρ (m + 1))
    (carrierFacetRestrictionData (G := G) K ρ (m + 1))
    (carrierPrimitiveSectionDataSucc (G := G) K m ρ)
    (carrierFacetRestrictionData_primitiveRes (G := G) K ρ (m + 1))

/-- Degree zero: the localized distribution quotient is trivial. -/
theorem simplexLocalTauZero_subsingleton (ρ : NonemptySimplex K) :
    Subsingleton
      (Tau (carrierFacetSets K ρ 0)
        (carrierFacetRestrictionData (G := G) K ρ 0)) := by
  exact GeneralSphereT.PathAlgebra.tau_subsingleton
    (carrierFacetSets K ρ 0)
    (carrierFacetRestrictionData (G := G) K ρ 0)
    (carrierPrimitiveSectionDataZero (G := G) K ρ)
    (carrierFacetRestrictionData_primitiveRes (G := G) K ρ 0)

/-- Uniform form in every cochain degree. -/
theorem simplexLocalTau_subsingleton (n : ℕ) (ρ : NonemptySimplex K) :
    Subsingleton
      (Tau (carrierFacetSets K ρ n)
        (carrierFacetRestrictionData (G := G) K ρ n)) := by
  cases n with
  | zero => exact simplexLocalTauZero_subsingleton (G := G) K ρ
  | succ m =>
      simpa [Nat.succ_eq_add_one] using
        simplexLocalTauSucc_subsingleton (G := G) K m ρ

/-- Representative form: every simplex-local `tau` class is zero. -/
theorem simplexLocalTau_eq_zero
    (n : ℕ) (ρ : NonemptySimplex K)
    (x : Tau (carrierFacetSets K ρ n)
      (carrierFacetRestrictionData (G := G) K ρ n)) :
    x = 0 :=
  @Subsingleton.elim _ (simplexLocalTau_subsingleton (G := G) K n ρ) x 0

end GeneralSphereT.SimplicialCochain
