import Formalization.CoefficientLocalZero
import Formalization.Section3SimplicialLocalTau
import Formalization.Section3ConeReplacementWord
import Formalization.Section3SimultaneousReplacement

set_option linter.style.header false

/-!
# Section 3: simultaneous apex replacement on a simplicial cone

This file joins the four ingredients of the Section 3 argument in the
concrete simplicial model.  We assume that `K` is a cone with apex `v`, in
the literal sense that adjoining `v` to every simplex of `K` again gives a
simplex.  The global facet family consists of all nonempty simplices
containing `v`; for `C_v M` these are precisely the simplices contained in
the usual apex facets, with repetitions harmless for the intersection of
restriction kernels.

For every elementary operator supported on an apex simplex, the closed-star
contraction produces an apex-free word with the same coboundary.  Local
vanishing of a physical path makes its coefficient distribution locally
invisible on the carrier of that simplex.  The simplex-local `tau` theorem
and the square-strip theorem therefore put the one-edge-minus-word error in
`E_id`.  Finally `simultaneousReplacement_exists` performs all replacements
in one finite sum.

The only model bridge left outside this file is the standard identification
of an externally presented cone `C_v M` with a complex satisfying
`IsConeAt K v`; no algebraic replacement step remains abstract.
-/

noncomputable section

namespace GeneralSphereT.SimplicialCochain

open GeneralSphereT.PathAlgebra
open GeneralSphereT.PathAlgebra.FacetRestrictionData

variable {V G : Type*} [LinearOrder V] [Fintype V] [AddCommGroup G]
variable (K : AbstractSimplicialComplex V)

/-! ## The concrete cone model -/

/-- Every simplex remains a simplex after adjoining the chosen apex. -/
def IsConeAt (v : V) : Prop :=
  ∀ σ : NonemptySimplex K, insert v σ.1 ∈ K

/-- The one-vertex simplex used to index the apex closed star and its facet
family. -/
def coneApexSimplex (v : V) : NonemptySimplex K :=
  ⟨{v}, K.singleton_mem v⟩

omit [LinearOrder V] [Fintype V] in
@[simp]
theorem coneApexSimplex_val (v : V) :
    (coneApexSimplex K v).1 = {v} :=
  rfl

omit [LinearOrder V] [Fintype V] in
@[simp]
theorem mem_coneApexSimplex (v : V) :
    v ∈ (coneApexSimplex K v).1 := by
  simp [coneApexSimplex]

omit [Fintype V] in
/-- On a cone, every simplex coordinate belongs to the apex closed star. -/
theorem simplex_mem_apexClosedStar
    {v : V} (hcone : IsConeAt K v) {n : ℕ} (σ : Simplex K n) :
    σ.1 ∪ (coneApexSimplex K v).1 ∈ K := by
  simpa [IsConeAt, coneApexSimplex, Finset.union_singleton] using
    hcone ⟨σ.1, σ.2.1⟩

/-- Restriction to the apex closed star is injective because that closed star
is the entire cone. -/
theorem restrictClosedStar_apex_injective
    {v : V} (hcone : IsConeAt K v) (n : ℕ) :
    Function.Injective
      (restrictClosedStar (G := G) K (coneApexSimplex K v) n) := by
  intro c c' h
  ext σ
  let σStar : ClosedStarSimplex K (coneApexSimplex K v) n :=
    ⟨σ, simplex_mem_apexClosedStar K hcone σ⟩
  exact DFunLike.congr_fun h σStar

/-- Extending a restricted cochain from the apex closed star changes
nothing, since there are no coordinates outside that star. -/
theorem extendCarrierClosedStar_restrict_apex
    {v : V} (hcone : IsConeAt K v) (n : ℕ) (c : Cochain K n G) :
    extendCarrierClosedStar K (coneApexSimplex K v) n
        (restrictClosedStar K (coneApexSimplex K v) n c) = c := by
  ext σ
  exact coordinateExtension_apply_mem
    (carrierClosedStarSet K (coneApexSimplex K v) n)
    (restrictClosedStar K (coneApexSimplex K v) n c)
    (simplex_mem_apexClosedStar K hcone σ)

/-! ## Moving the closed-star replacement back to global cochains -/

/-- The global bottom cochain: restrict to the apex closed star, apply
`h d`, and extend back.  On a cone both restriction and extension are
coordinate identifications. -/
def simplicialConeBottomReplacement
    (v : V) (n : ℕ) : Cochain K n G →ₗ[ℤ] Cochain K n G :=
  (extendCarrierClosedStar K (coneApexSimplex K v) n).toIntLinearMap.comp
    ((coneBottomReplacement K (coneApexSimplex K v) v
      (mem_coneApexSimplex K v) n).comp
      (restrictClosedStar K (coneApexSimplex K v) n))

@[simp]
theorem simplicialConeBottomReplacement_apply
    (v : V) (n : ℕ) (t : Cochain K n G) :
    simplicialConeBottomReplacement K v n t =
      extendCarrierClosedStar K (coneApexSimplex K v) n
        (coneBottomReplacement K (coneApexSimplex K v) v
          (mem_coneApexSimplex K v) n
          (restrictClosedStar K (coneApexSimplex K v) n t)) :=
  rfl

/-- The global bottom cochain has the same simplicial coboundary as the
original cochain. -/
theorem coboundary_simplicialConeBottomReplacement
    {v : V} (hcone : IsConeAt K v) (n : ℕ) (t : Cochain K n G) :
    coboundary K n (simplicialConeBottomReplacement K v n t) =
      coboundary K n t := by
  apply restrictClosedStar_apex_injective (G := G) K hcone (n + 1)
  have hleft := LinearMap.congr_fun
    (restrictClosedStar_coboundary (G := G) K
      (coneApexSimplex K v) n)
    (simplicialConeBottomReplacement K v n t)
  have hright := LinearMap.congr_fun
    (restrictClosedStar_coboundary (G := G) K
      (coneApexSimplex K v) n) t
  simp only [LinearMap.comp_apply] at hleft hright
  rw [hleft, hright]
  rw [simplicialConeBottomReplacement_apply,
    restrictClosedStar_extendCarrierClosedStar,
    closedStarCoboundary_coneBottomReplacement]

/-- Endpoint form with the physical group corestricted to the coboundary
range. -/
theorem coboundaryToRange_simplicialConeBottomReplacement
    {v : V} (hcone : IsConeAt K v) (n : ℕ) (t : Cochain K n G) :
    coboundaryToRange (G := G) K n
        (simplicialConeBottomReplacement K v n t) =
      coboundaryToRange K n t := by
  apply Subtype.ext
  exact coboundary_simplicialConeBottomReplacement K hcone n t

/-- A global coordinate in the support of the bottom cochain corresponds to
the same coordinate in the closed-star support. -/
theorem mem_closedStar_support_of_mem_simplicialConeBottom_support
    {v : V} (hcone : IsConeAt K v) (n : ℕ) (t : Cochain K n G)
    (σ : Simplex K n)
    (hσ : σ ∈ (simplicialConeBottomReplacement K v n t).support) :
    let σStar : ClosedStarSimplex K (coneApexSimplex K v) n :=
      ⟨σ, simplex_mem_apexClosedStar K hcone σ⟩
    σStar ∈
      (coneBottomReplacement K (coneApexSimplex K v) v
        (mem_coneApexSimplex K v) n
        (restrictClosedStar K (coneApexSimplex K v) n t)).support := by
  intro σStar
  apply Finsupp.mem_support_iff.mpr
  have hne := Finsupp.mem_support_iff.mp hσ
  let bottom := coneBottomReplacement K (coneApexSimplex K v) v
    (mem_coneApexSimplex K v) n
    (restrictClosedStar K (coneApexSimplex K v) n t)
  have heval :
      simplicialConeBottomReplacement K v n t σ = bottom σStar := by
    change restrictClosedStar K (coneApexSimplex K v) n
        (extendCarrierClosedStar K (coneApexSimplex K v) n bottom) σStar =
      bottom σStar
    exact DFunLike.congr_fun
      (restrictClosedStar_extendCarrierClosedStar
        (G := G) K (coneApexSimplex K v) n bottom) σStar
  rw [heval] at hne
  exact hne

/-- No coordinate of the global bottom cochain contains the apex. -/
theorem apex_not_mem_of_mem_simplicialConeBottom_support
    {v : V} (hcone : IsConeAt K v) (n : ℕ) (t : Cochain K n G)
    (σ : Simplex K n)
    (hσ : σ ∈ (simplicialConeBottomReplacement K v n t).support) :
    v ∉ σ.1 := by
  let σStar : ClosedStarSimplex K (coneApexSimplex K v) n :=
    ⟨σ, simplex_mem_apexClosedStar K hcone σ⟩
  have hσStar :=
    mem_closedStar_support_of_mem_simplicialConeBottom_support
      K hcone n t σ hσ
  exact apex_not_mem_of_mem_coneBottomReplacement_support
    K (coneApexSimplex K v) v (mem_coneApexSimplex K v) n
      (restrictClosedStar K (coneApexSimplex K v) n t) σStar hσStar

/-- Restricting a global one-coordinate cochain gives the same
one-coordinate cochain on the full apex closed star. -/
theorem restrictClosedStar_single_apex
    {v : V} (hcone : IsConeAt K v) (n : ℕ)
    (τ : Simplex K n) (g : G) :
    restrictClosedStar K (coneApexSimplex K v) n (Finsupp.single τ g) =
      Finsupp.single
        (⟨τ, simplex_mem_apexClosedStar K hcone τ⟩ :
          ClosedStarSimplex K (coneApexSimplex K v) n) g := by
  classical
  ext σ
  rw [restrictClosedStar_apply]
  let τStar : ClosedStarSimplex K (coneApexSimplex K v) n :=
    ⟨τ, simplex_mem_apexClosedStar K hcone τ⟩
  by_cases hτσ : τ = σ.1
  · have hStar : τStar = σ := by
      apply Subtype.ext
      exact hτσ
    change (Finsupp.single τ g) σ.1 = (Finsupp.single τStar g) σ
    calc
      (Finsupp.single τ g) σ.1 = g := by
        rw [hτσ]
        exact Finsupp.single_eq_same
      _ = (Finsupp.single τStar g) σ := by
        rw [← hStar]
        exact Finsupp.single_eq_same.symm
  · have hStar : τStar ≠ σ := by
      intro h
      exact hτσ (congrArg Subtype.val h)
    change (Finsupp.single τ g) σ.1 = (Finsupp.single τStar g) σ
    calc
      (Finsupp.single τ g) σ.1 = 0 :=
        Finsupp.single_eq_of_ne (Ne.symm hτσ)
      _ = (Finsupp.single τStar g) σ :=
        (Finsupp.single_eq_of_ne (Ne.symm hStar)).symm

/-- For an elementary apex label, every coordinate introduced by the global
bottom replacement contains the old non-apex face. -/
theorem erase_apex_subset_of_mem_simplicialConeBottom_single_support
    {v : V} (hcone : IsConeAt K v) (n : ℕ)
    (τ : Simplex K n) (hvτ : v ∈ τ.1) (g : G)
    (σ : Simplex K n)
    (hσ : σ ∈
      (simplicialConeBottomReplacement K v n (Finsupp.single τ g)).support) :
    τ.1.erase v ⊆ σ.1 := by
  let τStar : ClosedStarSimplex K (coneApexSimplex K v) n :=
    ⟨τ, simplex_mem_apexClosedStar K hcone τ⟩
  let σStar : ClosedStarSimplex K (coneApexSimplex K v) n :=
    ⟨σ, simplex_mem_apexClosedStar K hcone σ⟩
  have hσStar :=
    mem_closedStar_support_of_mem_simplicialConeBottom_support
      K hcone n (Finsupp.single τ g) σ hσ
  rw [restrictClosedStar_single_apex K hcone] at hσStar
  exact erase_apex_subset_of_mem_coneBottomReplacement_single_support
    K (coneApexSimplex K v) v (mem_coneApexSimplex K v) n
      τStar hvτ g σStar hσStar

/-! ## The global replacement word and its carrier control -/

/-- Any finite coordinate type may be used to order the replacement word;
the order has no mathematical significance. -/
local instance simplicialConeSimplexLinearOrder (n : ℕ) :
    LinearOrder (Simplex K n) := by
  classical
  exact linearOrderOfSTO WellOrderingRel

/-- The finite word of nonzero coordinate increments of the global bottom
cochain. -/
def simplicialConeBottomWord
    (v : V) (n : ℕ) (t : Cochain K n G) : List (Cochain K n G) :=
  activeCoordinateIncrements (simplicialConeBottomReplacement K v n t)

/-- Every letter of the global bottom word is elementary. -/
theorem simplicialConeBottomWord_isElementary
    (v : V) (n : ℕ) (t : Cochain K n G) :
    ∀ u ∈ simplicialConeBottomWord K v n t, IsElementaryLabel u := by
  intro u hu
  rcases List.mem_map.mp hu with ⟨σ, hσ, rfl⟩
  refine ⟨σ, simplicialConeBottomReplacement K v n t σ, ?_, rfl⟩
  exact Finsupp.mem_support_iff.mp (by
    simpa [simplicialConeBottomWord, activeCoordinateIncrements] using hσ)

/-- The replacement word sums to the global bottom cochain. -/
theorem wordIncrement_simplicialConeBottomWord
    (v : V) (n : ℕ) (t : Cochain K n G) :
    wordIncrement (simplicialConeBottomWord K v n t) =
      simplicialConeBottomReplacement K v n t := by
  exact wordIncrement_activeCoordinateIncrements
    (simplicialConeBottomReplacement K v n t)

/-- The replacement word has the same physical endpoint as its input. -/
theorem coboundaryToRange_wordIncrement_simplicialConeBottomWord
    {v : V} (hcone : IsConeAt K v) (n : ℕ) (t : Cochain K n G) :
    coboundaryToRange (G := G) K n
        (wordIncrement (simplicialConeBottomWord K v n t)) =
      coboundaryToRange K n t := by
  rw [wordIncrement_simplicialConeBottomWord,
    coboundaryToRange_simplicialConeBottomReplacement K hcone]

/-- A complete cochain label is apex-free when every active simplex avoids
the apex. -/
def ApexFreeLabel (v : V) (t : Cochain K n G) : Prop :=
  ∀ σ ∈ t.support, v ∉ σ.1

/-- Every letter of a bottom word is apex-free. -/
theorem simplicialConeBottomWord_apexFree
    {v : V} (hcone : IsConeAt K v) (n : ℕ) (t : Cochain K n G) :
    ∀ u ∈ simplicialConeBottomWord K v n t, ApexFreeLabel K v u := by
  intro u hu
  rcases List.mem_map.mp hu with ⟨σ, hσ, rfl⟩
  intro θ hθ
  have hvalue : Finsupp.single σ
      (simplicialConeBottomReplacement K v n t σ) θ ≠ 0 :=
    Finsupp.mem_support_iff.mp hθ
  have hθσ : θ = σ := by
    by_contra hne
    exact hvalue (by simp [hne])
  subst θ
  exact apex_not_mem_of_mem_simplicialConeBottom_support
    K hcone n t σ (by
      simpa [simplicialConeBottomWord, activeCoordinateIncrements] using hσ)

/-- Carrier control for a letter of the global replacement word. -/
theorem simplicialConeBottomWord_letter_coordinate
    {v : V} (hcone : IsConeAt K v) (n : ℕ)
    (τ : Simplex K n) (hvτ : v ∈ τ.1) (g : G)
    (u : Cochain K n G)
    (hu : u ∈ simplicialConeBottomWord K v n (Finsupp.single τ g)) :
    ∃ σ : Simplex K n,
      σ ∈ (simplicialConeBottomReplacement K v n
        (Finsupp.single τ g)).support ∧
      u = Finsupp.single σ
        (simplicialConeBottomReplacement K v n
          (Finsupp.single τ g) σ) ∧
      v ∉ σ.1 ∧ τ.1.erase v ⊆ σ.1 := by
  rcases List.mem_map.mp hu with ⟨σ, hσ, rfl⟩
  have hσsupport : σ ∈
      (simplicialConeBottomReplacement K v n
        (Finsupp.single τ g)).support := by
    simpa [simplicialConeBottomWord, activeCoordinateIncrements] using hσ
  exact ⟨σ, hσsupport, rfl,
    apex_not_mem_of_mem_simplicialConeBottom_support
      K hcone n _ σ hσsupport,
    erase_apex_subset_of_mem_simplicialConeBottom_single_support
      K hcone n τ hvτ g σ hσsupport⟩

/-! ## One apex label: local tau produces the replacement identity -/

/-- The global facet family on the cone: all nonempty simplices containing
the apex. -/
abbrev ConeFacet (v : V) := CarrierFacet K (coneApexSimplex K v)

/-- Global restriction data for the cone model. -/
abbrev coneFacetRestrictionData (v : V) (n : ℕ) :=
  carrierFacetRestrictionData (G := G) K (coneApexSimplex K v) n

/-- The carrier facets of an apex simplex embed into the global apex-facet
family. -/
def apexCarrierFacetEmbedding
    {v : V} {n : ℕ} (τ : Simplex K n) (hvτ : v ∈ τ.1) :
    CarrierFacet K ⟨τ.1, τ.2.1⟩ → ConeFacet K v :=
  fun ρ => ⟨ρ.1, (by
    intro x hx
    have hxv : x = v := by simpa [coneApexSimplex] using hx
    subst x
    exact ρ.2 hvτ)⟩

/-- A replacement letter visible on an apex facet forces the original apex
label to be visible on the same facet. -/
theorem simplicialConeBottomWord_visibility
    {v : V} (hcone : IsConeAt K v) (n : ℕ)
    (τ : Simplex K n) (hvτ : v ∈ τ.1)
    (g : G) (hg : g ≠ 0)
    (u : Cochain K n G)
    (hu : u ∈ simplicialConeBottomWord K v n (Finsupp.single τ g))
    (ρ : ConeFacet K v)
    (huρ : (coneFacetRestrictionData (G := G) K v n).primitiveRes ρ u ≠ 0) :
    (coneFacetRestrictionData (G := G) K v n).primitiveRes ρ
        (Finsupp.single τ g) ≠ 0 := by
  rw [carrierFacetRestrictionData_primitiveRes] at huρ ⊢
  change coordinateRestriction (facesIn K n ρ.1) u ≠ 0 at huρ
  change coordinateRestriction (facesIn K n ρ.1)
      (Finsupp.single τ g) ≠ 0
  rcases simplicialConeBottomWord_letter_coordinate
    K hcone n τ hvτ g u hu with ⟨σ, _, rfl, _, hbase⟩
  have hσρ : σ ∈ facesIn K n ρ.1 := by
    by_contra hnot
    exact huρ (coordinateRestriction_single_not_mem
      (facesIn K n ρ.1) hnot _)
  have hvρ : v ∈ ρ.1.1 := ρ.2 (by simp [coneApexSimplex])
  have hτρ : τ ∈ facesIn K n ρ.1 := by
    intro x hx
    by_cases hxv : x = v
    · simpa [hxv] using hvρ
    · exact hσρ (hbase (Finset.mem_erase.mpr ⟨hxv, hx⟩))
  rw [coordinateRestriction_single_mem (facesIn K n ρ.1) hτρ]
  exact Finsupp.single_ne_zero.mpr hg

/-- The coefficient distribution of an apex label in a locally zero
elementary physical path is an augmentation-zero distribution. -/
def apexPathCoefficientRedDist
    {v : V} {n : ℕ} (τ : Simplex K n) (hvτ : v ∈ τ.1)
    (g : G) (hg : g ≠ 0)
    (e : Path (Cochain K n G) (CoboundaryGroup (G := G) K n))
    (helem : e ∈ elementaryPaths
      (ι := Simplex K n) (G := G) (X := CoboundaryGroup (G := G) K n))
    (hlocal : e ∈ (coneFacetRestrictionData (G := G) K v n).locallyZeroPhysicalPath) :
    RedDist (CoboundaryGroup (G := G) K n) := by
  let self : ConeFacet K v :=
    ⟨⟨τ.1, τ.2.1⟩, by
      intro x hx
      have hxv : x = v := by simpa [coneApexSimplex] using hx
      simpa [hxv] using hvτ⟩
  let coeff := pathCoefficient (Finsupp.single τ g)
    (singleConfiguration_ne_zero τ hg) e
  have hzero :
      mapDist ((coneFacetRestrictionData (G := G) K v n).physicalRes self)
          coeff = 0 := by
    exact mapDist_pathCoefficient_eq_zero_of_locallyZeroPhysicalPath
      (carrierFacetSets K (coneApexSimplex K v) n)
      (coneFacetRestrictionData (G := G) K v n)
      (carrierFacetRestrictionData_primitiveRes
        (G := G) K (coneApexSimplex K v) n)
      helem hlocal τ g hg self Finset.Subset.rfl
  refine ⟨coeff, ?_⟩
  calc
    augmentation (CoboundaryGroup (G := G) K n) coeff =
        augmentation _
          (mapDist
            ((coneFacetRestrictionData (G := G) K v n).physicalRes self)
            coeff) := by
      symm
      exact LinearMap.congr_fun
        (augmentation_mapDist
          ((coneFacetRestrictionData (G := G) K v n).physicalRes self)) coeff
    _ = 0 := by rw [hzero]; simp

/-- The preceding reduced coefficient is locally invisible on every simplex
containing the active apex simplex. -/
theorem apexPathCoefficientRedDist_mem_localInvariant
    {v : V} {n : ℕ} (τ : Simplex K n) (hvτ : v ∈ τ.1)
    (g : G) (hg : g ≠ 0)
    (e : Path (Cochain K n G) (CoboundaryGroup (G := G) K n))
    (helem : e ∈ elementaryPaths
      (ι := Simplex K n) (G := G) (X := CoboundaryGroup (G := G) K n))
    (hlocal : e ∈ (coneFacetRestrictionData (G := G) K v n).locallyZeroPhysicalPath) :
    apexPathCoefficientRedDist K τ hvτ g hg e helem hlocal ∈
      FacetRestrictionData.physicalInvariantDistributions
        (carrierFacetRestrictionData (G := G) K ⟨τ.1, τ.2.1⟩ n) := by
  rw [physicalInvariantDistributions, Submodule.mem_iInf]
  intro ρ
  rw [LinearMap.mem_ker]
  let embed := apexCarrierFacetEmbedding K τ hvτ ρ
  apply Subtype.ext
  change mapDist
      ((carrierFacetRestrictionData (G := G) K ⟨τ.1, τ.2.1⟩ n).physicalRes ρ)
      (pathCoefficient (Finsupp.single τ g)
        (singleConfiguration_ne_zero τ hg) e) = 0
  have hzero := mapDist_pathCoefficient_eq_zero_of_locallyZeroPhysicalPath
    (carrierFacetSets K (coneApexSimplex K v) n)
    (coneFacetRestrictionData (G := G) K v n)
    (carrierFacetRestrictionData_primitiveRes
      (G := G) K (coneApexSimplex K v) n)
    helem hlocal τ g hg embed ρ.2
  exact hzero

/-- One elementary apex label can be replaced by the global bottom word;
its coefficientwise error belongs to `E_id`. -/
theorem apexLabelReplacementError_mem_physicalIdentityPaths
    {v : V} (hcone : IsConeAt K v) (n : ℕ)
    (τ : Simplex K n) (hvτ : v ∈ τ.1)
    (g : G) (hg : g ≠ 0)
    (e : Path (Cochain K n G) (CoboundaryGroup (G := G) K n))
    (helem : e ∈ elementaryPaths
      (ι := Simplex K n) (G := G) (X := CoboundaryGroup (G := G) K n))
    (hlocal : e ∈ (coneFacetRestrictionData (G := G) K v n).locallyZeroPhysicalPath) :
    ellDistribution (coboundaryToRange (G := G) K n)
        (Finsupp.single τ g)
        (simplicialConeBottomWord K v n (Finsupp.single τ g))
        (pathCoefficient (Finsupp.single τ g)
          (singleConfiguration_ne_zero τ hg) e) ∈
      physicalIdentityPaths (coneFacetRestrictionData (G := G) K v n) := by
  let z := apexPathCoefficientRedDist K τ hvτ g hg e helem hlocal
  have hzInv := apexPathCoefficientRedDist_mem_localInvariant
    K τ hvτ g hg e helem hlocal
  have hzSpan := simplexLocalInvariant_le_elementarySpan
    (G := G) K n ⟨τ.1, τ.2.1⟩ hzInv
  have hcarrier :
      ∀ ρ : ConeFacet K v,
        (coneFacetRestrictionData (G := G) K v n).primitiveRes ρ
            (Finsupp.single τ g) ≠ 0 →
        ∃ lf : CarrierFacet K ⟨τ.1, τ.2.1⟩,
          apexCarrierFacetEmbedding K τ hvτ lf = ρ := by
    intro ρ hρ
    rw [carrierFacetRestrictionData_primitiveRes] at hρ
    have hτρ : τ ∈ facesIn K n ρ.1 := by
      by_contra hnot
      exact hρ (coordinateRestriction_single_not_mem
        (facesIn K n ρ.1) hnot _)
    let lf : CarrierFacet K ⟨τ.1, τ.2.1⟩ := ⟨ρ.1, hτρ⟩
    refine ⟨lf, ?_⟩
    apply Subtype.ext
    rfl
  have herror :=
    ellRedDistribution_elementaryCarrierCubeSpan_mem
      (coneFacetRestrictionData (G := G) K v n)
      (carrierFacetRestrictionData_primitiveRes
        (G := G) K (coneApexSimplex K v) n)
      (apexCarrierFacetEmbedding K τ hvτ)
      (fun _ => rfl)
      (Finsupp.single τ g)
      (simplicialConeBottomWord K v n (Finsupp.single τ g))
      ⟨τ, g, hg, rfl⟩
      (simplicialConeBottomWord_isElementary K v n _)
      (coboundaryToRange_wordIncrement_simplicialConeBottomWord
        K hcone n _)
      (simplicialConeBottomWord_visibility K hcone n τ hvτ g hg)
      hcarrier hzSpan
  change ellRedDistribution
      (d := coboundaryToRange (G := G) K n)
      (Finsupp.single τ g)
      (simplicialConeBottomWord K v n (Finsupp.single τ g)) z ∈
    physicalIdentityPaths (coneFacetRestrictionData (G := G) K v n)
  exact herror

/-! ## Simultaneous replacement -/

/-- Every invariant elementary path on the cone is congruent modulo `E_id`
to an elementary path all of whose complete labels avoid the apex. -/
theorem simultaneousApexReplacement_exists
    {v : V} (hcone : IsConeAt K v) (n : ℕ)
    (e : Path (Cochain K n G) (CoboundaryGroup (G := G) K n))
    (he : e ∈ physicalInvariantPaths
      (coneFacetRestrictionData (G := G) K v n)) :
    ∃ ebot : Path (Cochain K n G) (CoboundaryGroup (G := G) K n),
      ebot ∈ restrictedElementaryPaths
        (B := CoboundaryGroup (G := G) K n) (ApexFreeLabel K v) ∧
      e - ebot ∈
        physicalIdentityPaths (coneFacetRestrictionData (G := G) K v n) := by
  apply simultaneousReplacement_exists
    (coneFacetRestrictionData (G := G) K v n)
    (ApexFreeLabel K v) e he.1
  intro r hr hrelem
  rcases hrelem with ⟨τ, g, hg, rfl⟩
  by_cases hvτ : v ∈ τ.1
  · refine ⟨simplicialConeBottomWord K v n (Finsupp.single τ g), ?_, ?_⟩
    · intro u hu
      exact ⟨simplicialConeBottomWord_isElementary K v n _ u hu,
        simplicialConeBottomWord_apexFree K hcone n _ u hu⟩
    · exact apexLabelReplacementError_mem_physicalIdentityPaths
        K hcone n τ hvτ g hg e he.1 he.2.2
  · refine ⟨[Finsupp.single τ g], ?_, ?_⟩
    · intro u hu
      have hu' : u = Finsupp.single τ g := by simpa using hu
      subst u
      refine ⟨⟨τ, g, hg, rfl⟩, ?_⟩
      intro σ hσ
      have hστ : σ = τ := by
        by_contra hne
        exact Finsupp.mem_support_iff.mp hσ (by simp [hne])
      simpa [hστ] using hvτ
    · have hell :
          ellDistribution (coboundaryToRange (G := G) K n)
              (Finsupp.single τ g) [Finsupp.single τ g]
              (pathCoefficient (Finsupp.single τ g)
                (singleConfiguration_ne_zero τ hg) e) = 0 := by
          let coeff := pathCoefficient (Finsupp.single τ g)
            (singleConfiguration_ne_zero τ hg) e
          change ellDistribution (coboundaryToRange (G := G) K n)
              (Finsupp.single τ g) [Finsupp.single τ g] coeff = 0
          induction coeff using Finsupp.induction with
          | zero => simp
          | single_add a z p ha hp ih =>
              rw [map_add, ih]
              simp [ellDistribution, ell, wordPath]
      rw [hell]
      exact (physicalIdentityPaths
        (coneFacetRestrictionData (G := G) K v n)).zero_mem

end GeneralSphereT.SimplicialCochain
