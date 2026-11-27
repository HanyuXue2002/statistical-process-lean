import Formalization.OpenDisk.NormalForm
import Formalization.ClosedPrimitiveImage
import Formalization.ElementaryPathCoefficientDecomposition

set_option linter.style.header false

/-!
# Constructive local normal form through the verified path complex

This is an alternative proof of Theorem 5.5.  Its potential is obtained by
projecting distributions onto their nonface cube coordinates and taking the
canonical ordered path.  The already verified closed-locally-zero path
theorem replaces the report's interchange of two extraction coordinates.
Both constructions use only fixed integral linear combinations of entries.
-/

noncomputable section

open scoped BigOperators
open GeneralSphereT.PathAlgebra

namespace OpenDisk

variable {ι G A Facet : Type*} [LinearOrder ι] [AddCommGroup G] [AddCommGroup A]

/-- The identity cochain model: primitive and physical configurations coincide. -/
def identityRestrictionData (facets : Facet → Set ι) :
    FacetRestrictionData
      (CAt := fun ρ => Configuration (facets ρ) G)
      (BAt := fun ρ => Configuration (facets ρ) G)
      (AddMonoidHom.id (Configuration ι G)) where
  primitiveRes := fun ρ => coordinateRestriction (facets ρ)
  physicalRes := fun ρ => coordinateRestriction (facets ρ)
  localD := fun ρ => AddMonoidHom.id _
  commutes := fun _ => rfl

/-- Retain exactly the no-facet coordinates in the integral cube basis. -/
def nonfaceProjection (facets : Facet → Set ι) :
    GeneralSphereT.PathAlgebra.Dist (Configuration ι G) →ₗ[ℤ]
      GeneralSphereT.PathAlgebra.Dist (Configuration ι G) := by
  classical
  exact (cubeBasis (ι := ι) (G := G)).constr ℤ
    (fun c => if c ∈ noFacetContainsCubeIndices facets then cubeDistribution c else 0)

theorem nonfaceProjection_cube (facets : Facet → Set ι) (c : Configuration ι G)
    (hc : c ∈ noFacetContainsCubeIndices facets) :
    nonfaceProjection facets (cubeDistribution c) = cubeDistribution c := by
  classical
  rw [← cubeBasis_apply]
  simp only [nonfaceProjection, Module.Basis.constr_basis, if_pos hc]
  exact (cubeBasis_apply c).symm

/-- The projection fixes the common restriction kernel, by its cube-basis description. -/
theorem nonfaceProjection_eq_self (facets : Facet → Set ι)
    (u : GeneralSphereT.PathAlgebra.Dist (Configuration ι G))
    (hu : u ∈ coordinateCommonRestrictionKernel (G := G) facets) :
    nonfaceProjection facets u = u := by
  classical
  rw [coordinateCommonRestrictionKernel_eq_noFacetCubeSpan, noFacetCubeSpan] at hu
  induction hu using Submodule.span_induction with
  | mem u hu =>
      obtain ⟨c, hc, rfl⟩ := hu
      rw [cubeBasis_apply, nonfaceProjection_cube facets c hc]
  | zero => simp
  | add u v hu hv ihu ihv => simp [ihu, ihv]
  | smul n u hu ih => simp [ih]

/-- A phase assigned additively to words of actual cochain operations. -/
abbrev OperationCharacter (ι G A : Type*) [AddCommGroup G] [AddCommGroup A] :=
  GeneralSphereT.PathAlgebra.Path (Configuration ι G) (Configuration ι G) →ₗ[ℤ] A

/-- The actual phase of one operation. Zero increments automatically have zero phase. -/
def operationPhase (L : OperationCharacter ι G A) (s c : Configuration ι G) : A :=
  L (edge s c)

/-- Operator locality is annihilation of the span of the explicitly defined
nonface iterated commutator squares. No conclusion about potentials is assumed. -/
def OperatorLocal (facets : Facet → Set ι) (L : OperationCharacter ι G A) : Prop :=
  physicalIdentityPaths (identityRestrictionData (G := G) facets) ≤ LinearMap.ker L

theorem operatorLocal_iff_generators (facets : Facet → Set ι)
    (L : OperationCharacter ι G A) :
    OperatorLocal facets L ↔
      ∀ i g j h rs c, g ≠ 0 → h ≠ 0 →
        NoCommonFacetList (fun ρ => coordinateRestriction (G := G) (facets ρ))
          (Finsupp.single i g :: Finsupp.single j h :: rs) →
        L (iteratedPhysicalLocalitySquare (AddMonoidHom.id (Configuration ι G))
          (Finsupp.single i g) (Finsupp.single j h) rs c) = 0 := by
  rw [OperatorLocal, physicalIdentityPaths, Submodule.span_le]
  constructor
  · intro h i g j k rs c hg hk hfac
    exact h ⟨i, g, j, k, rs, c, hg, hk, hfac, rfl⟩
  · intro h R hR
    obtain ⟨i, g, j, k, rs, c, hg, hk, hfac, rfl⟩ := hR
    exact h i g j k rs c hg hk hfac

theorem phaseDifference_commute (s t : Configuration ι G) (f : Configuration ι G → A) :
    phaseDifference s (phaseDifference t f) = phaseDifference t (phaseDifference s f) := by
  funext c
  simp only [phaseDifference]
  rw [show c + s + t = c + t + s by abel]
  abel

theorem iteratedPhaseDifference_phaseDifference (rs : List (Configuration ι G))
    (s : Configuration ι G) (f : Configuration ι G → A) :
    iteratedPhaseDifference rs (phaseDifference s f) =
      phaseDifference s (iteratedPhaseDifference rs f) := by
  induction rs generalizing f with
  | nil => rfl
  | cons r rs ih =>
      change iteratedPhaseDifference rs (phaseDifference r (phaseDifference s f)) =
        phaseDifference s (iteratedPhaseDifference rs (phaseDifference r f))
      rw [phaseDifference_commute r s f, ih]

/-- Evaluation of the path square is the phase of the actual binary commutator. -/
theorem operationCharacter_square (L : OperationCharacter ι G A)
    (s t c : Configuration ι G) :
    L (square (AddMonoidHom.id (Configuration ι G)) s t c) =
      phaseDifference s (operationPhase L t) c -
        phaseDifference t (operationPhase L s) c := by
  simp only [square, map_sub, map_add, AddMonoidHom.id_apply, operationPhase, phaseDifference]
  abel

/-- The generators are exactly the repeated phase differences in equation (5.2). -/
theorem operationCharacter_iterated_square (L : OperationCharacter ι G A)
    (s t : Configuration ι G) (rs : List (Configuration ι G)) (c : Configuration ι G) :
    L (iteratedPhysicalLocalitySquare (AddMonoidHom.id (Configuration ι G)) s t rs c) =
      iteratedPhaseDifference rs
        (fun v => phaseDifference s (operationPhase L t) v -
          phaseDifference t (operationPhase L s) v) c := by
  induction rs generalizing c with
  | nil => exact operationCharacter_square L s t c
  | cons r rs ih =>
      change L (iteratedBaseDifference (AddMonoidHom.id (Configuration ι G)) rs
        (baseDifference r (square (AddMonoidHom.id (Configuration ι G)) s t c))) = _
      have hsq : baseDifference r (square (AddMonoidHom.id (Configuration ι G)) s t c) =
          square (AddMonoidHom.id (Configuration ι G)) s t (c + r) -
            square (AddMonoidHom.id (Configuration ι G)) s t c :=
        baseDifference_square (AddMonoidHom.id (Configuration ι G)) r s t c
      rw [hsq, map_sub, map_sub]
      change L (iteratedPhysicalLocalitySquare (AddMonoidHom.id (Configuration ι G))
        s t rs (c + r)) - L (iteratedPhysicalLocalitySquare
          (AddMonoidHom.id (Configuration ι G)) s t rs c) = _
      rw [ih, ih]
      exact congrFun (iteratedPhaseDifference_phaseDifference rs r _).symm c

/-- The operator-local input in the constructive theorem is exactly the report's phase equations. -/
theorem operatorLocal_iff_phase_equations (facets : Facet → Set ι)
    (L : OperationCharacter ι G A) :
    OperatorLocal facets L ↔
      ∀ i g j h rs c, g ≠ 0 → h ≠ 0 →
        NoCommonFacetList (fun ρ => coordinateRestriction (G := G) (facets ρ))
          (Finsupp.single i g :: Finsupp.single j h :: rs) →
        iteratedPhaseDifference rs
          (fun v => phaseDifference (Finsupp.single i g) (operationPhase L (Finsupp.single j h)) v -
            phaseDifference (Finsupp.single j h) (operationPhase L (Finsupp.single i g)) v) c = 0 := by
  simp only [operatorLocal_iff_generators, operationCharacter_iterated_square]

/-- The fixed, linear choice of potential used in this proof of Theorem 5.5. -/
def normalPotential (facets : Facet → Set ι) (L : OperationCharacter ι G A)
    (c : Configuration ι G) : A :=
  L (rawCanonicalPath (nonfaceProjection facets (Finsupp.single c 1)))

theorem phasePairing_normalPotential (facets : Facet → Set ι)
    (L : OperationCharacter ι G A) :
    phasePairing (normalPotential facets L) =
      L.comp (rawCanonicalPath.comp (nonfaceProjection facets)) := by
  ext c
  simp [normalPotential]

theorem phasePairing_operationPhase (L : OperationCharacter ι G A)
    (s : Configuration ι G) :
    phasePairing (operationPhase L s) = L.comp (edgeDistribution s) := by
  ext c
  simp [operationPhase]

theorem mapPath_edgeDistribution {κ H : Type*} [AddCommGroup H]
    (i b : Configuration ι G →+ Configuration κ H) (s : Configuration ι G) :
    (mapPath i b).comp (edgeDistribution s) =
      (edgeDistribution (i s)).comp (mapDist b) := by
  ext c
  simp

theorem primitiveBoundary_edgeDistribution (s : Configuration ι G) :
    (primitiveBoundary (Configuration ι G)).comp (edgeDistribution s) =
      distributionDifference s := by
  ext c
  simp [bracket]

theorem edgeDistribution_elementary (i : ι) (g : G) (hg : g ≠ 0)
    (u : GeneralSphereT.PathAlgebra.Dist (Configuration ι G)) :
    edgeDistribution (Finsupp.single i g) u ∈
      elementaryPaths (ι := ι) (G := G) (X := Configuration ι G) := by
  classical
  induction u using Finsupp.induction with
  | zero => simp
  | single_add c n u hc hn ih =>
      rw [map_add, edgeDistribution_single]
      exact Submodule.add_mem _ (Submodule.smul_mem _ n (elementaryEdge_mem i hg c)) ih

/-- A marked-invisible coefficient distribution gives a globally invisible operation word. -/
theorem edgeDistribution_markedKernel (facets : Facet → Set ι) (i : ι) (g : G)
    (u : GeneralSphereT.PathAlgebra.Dist (Configuration ι G))
    (hu : u ∈ coordinateCommonRestrictionKernel (G := G) (markedFacets facets {i})) :
    edgeDistribution (Finsupp.single i g) u ∈
      (identityRestrictionData (G := G) facets).locallyZeroPrimitivePath := by
  rw [FacetRestrictionData.locallyZeroPrimitivePath, Submodule.mem_iInf]
  intro ρ
  change mapPath (coordinateRestriction (facets ρ)) (coordinateRestriction (facets ρ))
    (edgeDistribution (Finsupp.single i g) u) = 0
  rw [← LinearMap.comp_apply, mapPath_edgeDistribution, LinearMap.comp_apply]
  classical
  by_cases hi : i ∈ facets ρ
  · let ρ' : {ρ : Facet // ∀ j ∈ ({i} : Finset ι), j ∈ facets ρ} :=
      ⟨ρ, by simpa using hi⟩
    have huρ := (Submodule.mem_iInf (fun σ =>
      LinearMap.ker (mapDist (coordinateRestriction (markedFacets facets {i} σ))))).mp hu ρ'
    change mapDist (coordinateRestriction (facets ρ)) u = 0 at huρ
    simp [huρ]
  · rw [coordinateRestriction_single_not_mem (facets ρ) hi]
    have hz : edgeDistribution (X := Configuration (facets ρ) G)
        (0 : Configuration (facets ρ) G) = 0 := by
      ext c
      simp
    simp [hz]

/-- Boundary sends locally invisible paths to the common restriction kernel. -/
theorem primitiveBoundary_mem_commonKernel (facets : Facet → Set ι)
    (p : GeneralSphereT.PathAlgebra.Path (Configuration ι G) (Configuration ι G))
    (hp : p ∈ (identityRestrictionData (G := G) facets).locallyZeroPrimitivePath) :
    primitiveBoundary (Configuration ι G) p ∈ coordinateCommonRestrictionKernel (G := G) facets := by
  rw [coordinateCommonRestrictionKernel, Submodule.mem_iInf]
  intro ρ
  have hpρ := (Submodule.mem_iInf (fun σ =>
    LinearMap.ker ((identityRestrictionData (G := G) facets).restrictPrimitivePath σ))).mp hp ρ
  change mapPath (coordinateRestriction (facets ρ)) (coordinateRestriction (facets ρ)) p = 0 at hpρ
  change mapDist (coordinateRestriction (facets ρ)) (primitiveBoundary (Configuration ι G) p) = 0
  have hn := LinearMap.congr_fun (boundary_natural
    (AddMonoidHom.id (Configuration ι G)) (AddMonoidHom.id (Configuration (facets ρ) G))
    (coordinateRestriction (facets ρ)) (coordinateRestriction (facets ρ)) rfl) p
  simpa [hpρ] using hn

theorem rawCanonicalPath_mem_local (facets : Facet → Set ι)
    (u : GeneralSphereT.PathAlgebra.Dist (Configuration ι G))
    (hu : u ∈ coordinateCommonRestrictionKernel (G := G) facets) :
    rawCanonicalPath u ∈ (identityRestrictionData (G := G) facets).locallyZeroPrimitivePath := by
  rw [FacetRestrictionData.locallyZeroPrimitivePath, Submodule.mem_iInf]
  intro ρ
  have huρ := (Submodule.mem_iInf (fun σ =>
    LinearMap.ker (mapDist (coordinateRestriction (facets σ))))).mp hu ρ
  change mapDist (coordinateRestriction (facets ρ)) u = 0 at huρ
  change mapPath (coordinateRestriction (facets ρ)) (coordinateRestriction (facets ρ))
    (rawCanonicalPath u) = 0
  have hn := LinearMap.congr_fun (rawCanonicalPath_coordinateRestriction (facets ρ)) u
  simpa [huρ] using hn

/-- The cochain square identities kill every closed, elementary, locally zero word. -/
theorem OperatorLocal.closed_word_zero (facets : Facet → Set ι)
    (hcover : ∀ i, ∃ ρ, i ∈ facets ρ) (L : OperationCharacter ι G A)
    (hL : OperatorLocal facets L)
    (p : GeneralSphereT.PathAlgebra.Path (Configuration ι G) (Configuration ι G))
    (helem : p ∈ elementaryPaths (ι := ι) (G := G) (X := Configuration ι G))
    (hclosed : primitiveReducedBoundary (Configuration ι G) p = 0)
    (hlocal : p ∈ (identityRestrictionData (G := G) facets).locallyZeroPrimitivePath) :
    L p = 0 := by
  have hp := mapDPath_mem_physicalIdentityPaths_of_closed_elementary_locallyZero
    facets (identityRestrictionData (G := G) facets) (fun _ => rfl) hcover helem hclosed hlocal
  have hid : mapDPath (AddMonoidHom.id (Configuration ι G)) =
      LinearMap.id (R := ℤ) (M := GeneralSphereT.PathAlgebra.Path
        (Configuration ι G) (Configuration ι G)) := by
    ext q
    change mapDPath (AddMonoidHom.id (Configuration ι G)) (edge q.1 q.2) = edge q.1 q.2
    simp
  rw [hid, LinearMap.id_apply] at hp
  exact hL hp

/-- On locally invisible elementary words, the operation phase is recovered
by the canonical primitive of the boundary. -/
theorem OperatorLocal.canonical_boundary (facets : Facet → Set ι)
    (hcover : ∀ i, ∃ ρ, i ∈ facets ρ) (L : OperationCharacter ι G A)
    (hL : OperatorLocal facets L)
    (p : GeneralSphereT.PathAlgebra.Path (Configuration ι G) (Configuration ι G))
    (helem : p ∈ elementaryPaths (ι := ι) (G := G) (X := Configuration ι G))
    (hlocal : p ∈ (identityRestrictionData (G := G) facets).locallyZeroPrimitivePath) :
    L p = L (rawCanonicalPath (primitiveBoundary (Configuration ι G) p)) := by
  let v := primitiveBoundary (Configuration ι G) p
  have hvaug : augmentation (Configuration ι G) v = 0 :=
    LinearMap.congr_fun (augmentation_boundary (AddMonoidHom.id (Configuration ι G))) p
  have hvlocal := primitiveBoundary_mem_commonKernel facets p hlocal
  have hbcanon : primitiveBoundary (Configuration ι G) (rawCanonicalPath v) = v := by
    rw [← LinearMap.comp_apply, primitiveBoundary_rawCanonicalPath, bracketCombination_apply,
      hvaug, zero_smul, sub_zero]
  have hzero := hL.closed_word_zero facets hcover L
    (p - rawCanonicalPath v)
    (Submodule.sub_mem _ helem (rawCanonicalPath_mem v))
    (by
      apply Subtype.ext
      change primitiveBoundary (Configuration ι G) (p - rawCanonicalPath v) = 0
      rw [map_sub, hbcanon]
      exact sub_self _)
    (Submodule.sub_mem _ hlocal (rawCanonicalPath_mem_local facets v hvlocal))
  exact sub_eq_zero.mp (by simpa only [map_sub] using hzero)

theorem phasePairing_sub (f g : Configuration ι G → A) :
    phasePairing (fun c => f c - g c) = phasePairing f - phasePairing g := by
  ext c
  simp

/-- The residual operation after conjugating by the chosen diagonal phase. -/
def normalResidual (facets : Facet → Set ι) (L : OperationCharacter ι G A)
    (i : ι) (g : G) : Configuration ι G → A := fun c =>
  operationPhase L (Finsupp.single i g) c -
    phaseDifference (Finsupp.single i g) (normalPotential facets L) c

/-- The constructive local normal form: every residual operation is marked-local. -/
theorem normalResidual_markedLocal (facets : Facet → Set ι)
    (hcover : ∀ i, ∃ ρ, i ∈ facets ρ) (L : OperationCharacter ι G A)
    (hL : OperatorLocal facets L) (i : ι) (g : G) (hg : g ≠ 0) :
    MarkedLocal facets {i} (normalResidual facets L i g) := by
  apply (anchoredLocal_iff_annihilates_commonKernel (markedFacets facets {i}) _).mpr
  intro u hu
  have hplocal := edgeDistribution_markedKernel facets i g u hu
  have hpel := edgeDistribution_elementary i g hg u
  have hcanonical := hL.canonical_boundary facets hcover L
    (edgeDistribution (Finsupp.single i g) u) hpel hplocal
  have hvlocal := primitiveBoundary_mem_commonKernel facets _ hplocal
  have hv : primitiveBoundary (Configuration ι G)
      (edgeDistribution (Finsupp.single i g) u) =
      distributionDifference (Finsupp.single i g) u :=
    LinearMap.congr_fun (primitiveBoundary_edgeDistribution _) u
  rw [hv] at hcanonical hvlocal
  change phasePairing (fun c => operationPhase L (Finsupp.single i g) c -
    phaseDifference (Finsupp.single i g) (normalPotential facets L) c) u = 0
  rw [phasePairing_sub, LinearMap.sub_apply,
    phasePairing_operationPhase, phasePairing_phaseDifference,
    phasePairing_normalPotential]
  simp only [LinearMap.comp_apply]
  rw [nonfaceProjection_eq_self facets _ hvlocal]
  exact sub_eq_zero.mpr hcanonical

/-- Theorem 5.5, with explicit integral choices and the actual locality-square hypothesis. -/
theorem local_normal_form (facets : Facet → Set ι)
    (hcover : ∀ i, ∃ ρ, i ∈ facets ρ) (L : OperationCharacter ι G A)
    (hL : OperatorLocal facets L) :
    ∃ (β : Configuration ι G → A) (O : ι → G → Configuration ι G → A),
      (∀ i g, g ≠ 0 → MarkedLocal facets {i} (O i g)) ∧
      (∀ i g c, operationPhase L (Finsupp.single i g) c =
        O i g c + phaseDifference (Finsupp.single i g) β c) := by
  refine ⟨normalPotential facets L, normalResidual facets L, ?_, ?_⟩
  · exact normalResidual_markedLocal facets hcover L hL
  · intro i g c
    exact (sub_add_cancel _ _).symm

theorem normalPotential_add (facets : Facet → Set ι) (L M : OperationCharacter ι G A) :
    normalPotential facets (L + M) = normalPotential facets L + normalPotential facets M := by
  funext c
  rfl

theorem normalResidual_add (facets : Facet → Set ι) (L M : OperationCharacter ι G A)
    (i : ι) (g : G) :
    normalResidual facets (L + M) i g = normalResidual facets L i g + normalResidual facets M i g := by
  funext c
  simp only [normalResidual, operationPhase, phaseDifference, normalPotential, LinearMap.add_apply,
    Pi.add_apply]
  abel

end OpenDisk
