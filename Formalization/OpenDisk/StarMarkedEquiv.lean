import Formalization.OpenDisk.StarMarkedTopology

set_option linter.style.header false

/-!
# The full star factors in the symmetry-kernel formula

Restriction and pullback are mutually inverse continuous additive maps
between globally closed marked hopping rows and closed local phases on the
geometric star. Constants are retained in both directions. This supplies
the literal star factors, not only their path connectedness.
-/

noncomputable section

open scoped BigOperators
open GeneralSphereT.PathAlgebra GeneralSphereT.SimplicialCochain

namespace OpenDisk.StarLocality

variable {V G P : Type*} [LinearOrder V] [Fintype V]
  [AddCommGroup G] [AddCommGroup P] [TopologicalSpace P] [IsTopologicalAddGroup P]

variable (K : AbstractSimplicialComplex V) (n : ℕ)

local instance equivFaceOrder : LinearOrder (Simplex K n) := by
  classical
  exact linearOrderOfSTO WellOrderingRel

local instance equivCarrierFintype (η : Simplex K n) : Fintype (CarrierFacets K n η) :=
  Fintype.ofFinite _

/-- The containing-simplex family covers every actual closed-star simplex. -/
theorem carrierFacets_cover_closedStar (η : Simplex K n) (k : ℕ)
    (τ : ClosedStarSimplex K (forgetDimension K η) k) :
    ∃ ρ : CarrierFacets K n η, τ.val.val ⊆ ρ.val.val := by
  refine ⟨⟨⟨τ.val.val ∪ η.val, τ.property⟩, ?_⟩, Finset.subset_union_left⟩
  intro i hi
  have heq : i = η := Finset.mem_singleton.mp hi
  subst i
  exact Finset.subset_union_right

def closedStarPhases (η : Simplex K n) :
    AddSubgroup (ClosedStarCochain K (forgetDimension K η) n G → P) where
  carrier := {f | ConePhaseLocal.StarLocal K (forgetDimension K η)
      (fun ρ : CarrierFacets K n η => ρ.val) (carrierFacetContains K n η) n f ∧
    ∀ (z : ConePhaseSimplicial.closedCochains (G := G) K (forgetDimension K η) n) c,
      f (c + z) = f c}
  zero_mem' := ⟨⟨0, fun c => by simp⟩, fun z c => rfl⟩
  add_mem' := by
    rintro f g ⟨⟨a, ha⟩, hf⟩ ⟨⟨b, hb⟩, hg⟩
    refine ⟨⟨a + b, fun c => ?_⟩, fun z c => ?_⟩
    · simp only [Pi.add_apply, ha c, hb c, Finset.sum_add_distrib]
    · simp only [Pi.add_apply, hf z c, hg z c]
  neg_mem' := by
    rintro f ⟨⟨a, ha⟩, hf⟩
    refine ⟨⟨-a, fun c => ?_⟩, fun z c => ?_⟩
    · simp only [Pi.neg_apply, ha c, Finset.sum_neg_distrib]
    · simp only [Pi.neg_apply, hf z c]

abbrev ClosedStarPhase (η : Simplex K n) := closedStarPhases (G := G) (P := P) K n η

theorem starPhase_pullback_marked (η : Simplex K n) (f : ClosedStarPhase (G := G) (P := P) K n η) :
    MarkedLocal (simplicialFacets K n) {η}
      (fun c => f.val (restrictClosedStar K (forgetDimension K η) n c)) := by
  obtain ⟨g, hg⟩ := f.property.1
  apply (differenceLocal_iff_anchoredLocal _ _).mp
  apply (differenceLocal_iff_facetSum _ _).mpr
  refine ⟨g, fun c => ?_⟩
  change f.val (restrictClosedStar K (forgetDimension K η) n c) =
    ∑ ρ : CarrierFacets K n η, g ρ (restrictCochain K n ρ.val c)
  rw [hg]
  apply Finset.sum_congr rfl
  intro ρ hρ
  exact congrArg (g ρ) (restrictSimplex_restrictStar K _ _ (carrierFacetContains K n η ρ) n c)

theorem starPhase_pullback_closed (η : Simplex K n) (f : ClosedStarPhase (G := G) (P := P) K n η) :
    phaseDerivative (coboundaryToRange (G := G) K n)
      (fun c => f.val (restrictClosedStar K (forgetDimension K η) n c)) = 0 := by
  ext z c
  have hz : coboundary K n (z : Cochain K n G) = 0 := congrArg Subtype.val z.property
  have hs : closedStarCoboundary K (forgetDimension K η) n
      (restrictClosedStar K (forgetDimension K η) n (z : Cochain K n G)) = 0 := by
    have hh := LinearMap.congr_fun
      (restrictClosedStar_coboundary (G := G) K (forgetDimension K η) n) z.val
    simpa only [LinearMap.comp_apply, hz, map_zero] using hh.symm
  let zs : ConePhaseSimplicial.closedCochains (G := G) K (forgetDimension K η) n :=
    ⟨restrictClosedStar K (forgetDimension K η) n z.val, hs⟩
  change f.val (restrictClosedStar K (forgetDimension K η) n (c + z)) -
    f.val (restrictClosedStar K (forgetDimension K η) n c) = 0
  rw [map_add]
  exact sub_eq_zero.mpr (f.property.2 zs _)

/-- Full-table restriction to the star is a homeomorphism onto closed local star phases. -/
def closedMarkedRowStarHomeomorph (η : Simplex K n) :
    ClosedMarkedRow (G := G) (P := P) K n η ≃ₜ ClosedStarPhase (G := G) (P := P) K n η where
  toFun f := ⟨restrictedMarkedPhase K n η f.val,
    restrictedMarkedPhase_starLocal K n η f.val f.property.1,
    restrictedMarkedPhase_closed K n η f.val f.property.1 f.property.2⟩
  invFun f := ⟨fun c => f.val (restrictClosedStar K (forgetDimension K η) n c),
    starPhase_pullback_marked K n η f, starPhase_pullback_closed K n η f⟩
  left_inv f := Subtype.ext (funext fun c => (marked_phase_factor K n η f.val f.property.1 c).symm)
  right_inv f := by
    apply Subtype.ext
    funext c
    change f.val (restrictClosedStar K (forgetDimension K η) n
      (extendCarrierClosedStar K (forgetDimension K η) n c)) = f.val c
    rw [restrictClosedStar_extendCarrierClosedStar]
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact continuous_pi fun c => (continuous_apply
      (extendCarrierClosedStar K (forgetDimension K η) n c)).comp continuous_subtype_val
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact continuous_pi fun c => (continuous_apply
      (restrictClosedStar K (forgetDimension K η) n c)).comp continuous_subtype_val

/-- The same star correspondence is additive, without quotienting constants. -/
def closedMarkedRowStarEquiv (η : Simplex K n) :
    ClosedMarkedRow (G := G) (P := P) K n η ≃+ ClosedStarPhase (G := G) (P := P) K n η where
  toEquiv := (closedMarkedRowStarHomeomorph (G := G) (P := P) K n η).toEquiv
  map_add' _ _ := rfl

def closedMarkedHoppingsStarHomeomorph :
    closedMarkedHoppings (coboundaryToRange (G := G) K n)
      (markedFunctionSubgroup (P := P) (simplicialFacets K n)) ≃ₜ
      (∀ e : ElementaryLabel (Simplex K n) G, ClosedStarPhase (G := G) (P := P) K n e.val.1) :=
  (closedMarkedHoppingsHomeomorph (G := G) (P := P) K n).trans
    (Homeomorph.piCongrRight fun e => closedMarkedRowStarHomeomorph K n e.val.1)

def closedMarkedHoppingsStarEquiv :
    closedMarkedHoppings (coboundaryToRange (G := G) K n)
      (markedFunctionSubgroup (P := P) (simplicialFacets K n)) ≃+
      (∀ e : ElementaryLabel (Simplex K n) G, ClosedStarPhase (G := G) (P := P) K n e.val.1) where
  toEquiv := (closedMarkedHoppingsStarHomeomorph (G := G) (P := P) K n).toEquiv
  map_add' _ _ := rfl

/-- The literal topological product in equation (5.5), for actual simplicial stars. -/
def symmetryKernelStarHomeomorph
    (rep : CoboundaryGroup (G := G) K n → Cochain K n G)
    (hrep : ∀ a, coboundaryToRange K n (rep a) = a) :
    (forgetSymmetry (coboundaryToRange (G := G) K n) elementaryStep
      (markedFunctionSubgroup (P := P) (simplicialFacets K n))).ker ≃ₜ
      (CoboundaryGroup (G := G) K n → P) ×
        (∀ e : ElementaryLabel (Simplex K n) G, ClosedStarPhase (G := G) (P := P) K n e.val.1) :=
  (symmetryKernelHomeomorph (coboundaryToRange (G := G) K n) elementaryStep
    (markedFunctionSubgroup (P := P) (simplicialFacets K n)) rep hrep).trans
    (Homeomorph.prodCongr (Homeomorph.refl _) (closedMarkedHoppingsStarHomeomorph K n))

def symmetryKernelStarEquiv
    (rep : CoboundaryGroup (G := G) K n → Cochain K n G)
    (hrep : ∀ a, coboundaryToRange K n (rep a) = a) :
    (forgetSymmetry (coboundaryToRange (G := G) K n) elementaryStep
      (markedFunctionSubgroup (P := P) (simplicialFacets K n))).ker ≃+
      (CoboundaryGroup (G := G) K n → P) ×
        (∀ e : ElementaryLabel (Simplex K n) G, ClosedStarPhase (G := G) (P := P) K n e.val.1) :=
  (symmetryKernelEquiv (coboundaryToRange (G := G) K n) elementaryStep
    (markedFunctionSubgroup (P := P) (simplicialFacets K n)) rep hrep).trans
    (AddEquiv.prodCongr (AddEquiv.refl _) (closedMarkedHoppingsStarEquiv K n))

theorem continuous_symmetryKernelStarEquiv
    (rep : CoboundaryGroup (G := G) K n → Cochain K n G)
    (hrep : ∀ a, coboundaryToRange K n (rep a) = a) :
    Continuous (symmetryKernelStarEquiv (G := G) (P := P) K n rep hrep) :=
  (symmetryKernelStarHomeomorph (G := G) (P := P) K n rep hrep).continuous_toFun

theorem continuous_symmetryKernelStarEquiv_symm
    (rep : CoboundaryGroup (G := G) K n → Cochain K n G)
    (hrep : ∀ a, coboundaryToRange K n (rep a) = a) :
    Continuous (symmetryKernelStarEquiv (G := G) (P := P) K n rep hrep).symm :=
  (symmetryKernelStarHomeomorph (G := G) (P := P) K n rep hrep).continuous_invFun

end OpenDisk.StarLocality
