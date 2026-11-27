import Formalization.Section4TopologicalComparisons

set_option linter.style.header false

/-!
# Section 4: the cone criterion for pointed null maps

This file formalizes the short argument proving (4.6).  The types `R` and
`Maps` are already based objects.  A null map is, by definition of the
pointed cone criterion, the restriction of an admissible cone map.  Primitive
relations extend to the cone, while cone vanishing and the degree-zero exact
row imply that every admissible cone map has a primitive lift.  Naturality of
restriction then identifies the two images.

No topology is hidden in the proof.  The explicit fields are precisely the
standard cone-extension maps whose construction depends on the chosen model.
-/

noncomputable section

namespace GeneralSphereT.Section4

universe uR uM uRC uMC uQC

variable {R : Type uR} {Maps : Type uM}
variable {RCone : Type uRC} {ConeMaps : Type uMC} {QCone : Type uQC}
variable [AddCommGroup R] [AddCommGroup Maps]
variable [AddCommGroup RCone] [AddCommGroup ConeMaps] [AddCommGroup QCone]

/-- The linear maps used by the pointed cone criterion.  The codomains are
already restricted by the basepoint conditions, so no additional predicates
occur in the algebra below. -/
structure ConeCriterionData
    (ρ : R →ₗ[ℤ] Maps) (ρCone : RCone →ₗ[ℤ] ConeMaps) where
  restrictRelation : RCone →ₗ[ℤ] R
  restrictMap : ConeMaps →ₗ[ℤ] Maps
  extendRelation : R →ₗ[ℤ] RCone
  restrict_extend : restrictRelation.comp extendRelation = LinearMap.id
  restriction_natural : restrictMap.comp ρCone = ρ.comp restrictRelation

namespace ConeCriterionData

variable {ρ : R →ₗ[ℤ] Maps} {ρCone : RCone →ₗ[ℤ] ConeMaps}
variable (C : ConeCriterionData ρ ρCone)

/-- Pointed null maps in the cone model: restrictions of admissible maps on
the cone. -/
abbrev coneNullMaps : Submodule ℤ Maps := LinearMap.range C.restrictMap

/-- If the final group in the cone degree-zero row vanishes, exactness makes
primitive restriction onto all admissible cone maps. -/
theorem coneRestriction_surjective
    (ωCone : ConeMaps →ₗ[ℤ] QCone)
    (hexact : Function.Exact ρCone ωCone)
    (hzero : ∀ x : QCone, x = 0) :
    Function.Surjective ρCone := by
  intro f
  have hf : ωCone f = 0 := hzero (ωCone f)
  exact (hexact f).mp hf

/-- Equation (4.6): primitive restrictions are exactly pointed null maps. -/
theorem range_restriction_eq_coneNullMaps
    (hρCone : Function.Surjective ρCone) :
    LinearMap.range ρ = C.coneNullMaps := by
  apply le_antisymm
  · rintro f ⟨r, rfl⟩
    refine ⟨ρCone (C.extendRelation r), ?_⟩
    have hnat := LinearMap.congr_fun C.restriction_natural
      (C.extendRelation r)
    have hext := LinearMap.congr_fun C.restrict_extend r
    calc
      C.restrictMap (ρCone (C.extendRelation r)) =
          ρ (C.restrictRelation (C.extendRelation r)) := by
        simpa using hnat
      _ = ρ r := by simpa using congrArg ρ hext
  · rintro f ⟨H, rfl⟩
    rcases hρCone H with ⟨r, hr⟩
    refine ⟨C.restrictRelation r, ?_⟩
    have hnat := LinearMap.congr_fun C.restriction_natural r
    calc
      ρ (C.restrictRelation r) = C.restrictMap (ρCone r) := by
        simpa using hnat.symm
      _ = C.restrictMap H := by rw [hr]

/-- The form used directly by Proposition 4.3: cone exactness and cone
vanishing imply the required null-map equality. -/
theorem range_restriction_eq_coneNullMaps_of_exact
    (ωCone : ConeMaps →ₗ[ℤ] QCone)
    (hexact : Function.Exact ρCone ωCone)
    (hzero : ∀ x : QCone, x = 0) :
    LinearMap.range ρ = C.coneNullMaps :=
  C.range_restriction_eq_coneNullMaps
    (coneRestriction_surjective (ρCone := ρCone)
      ωCone hexact hzero)

end ConeCriterionData

section ThetaFromCone

universe uZ uA uQ

variable {Cycles : Type uZ} {A : Type uA} {Q : Type uQ}
variable [AddCommGroup Cycles] [AddCommGroup A] [AddCommGroup Q]
variable {i : Cycles →ₗ[ℤ] R} {ρ : R →ₗ[ℤ] Maps}
variable {ω : Maps →ₗ[ℤ] Q} {ρCone : RCone →ₗ[ℤ] ConeMaps}

/-- Proposition 4.3 obtained directly from the two cone inputs: primitive
relations extend to the cone, and the cone obstruction group vanishes. -/
def thetaFromConeCriterion
    (based : BasedRowData A i ρ)
    (C : ConeCriterionData based.basedRestriction ρCone)
    (hexact : Function.Exact ρ ω)
    (hω : Function.Surjective ω)
    (ωCone : ConeMaps →ₗ[ℤ] QCone)
    (hconeExact : Function.Exact ρCone ωCone)
    (hconeZero : ∀ x : QCone, x = 0) :
    Q ≃ₗ[ℤ]
      PointedHomotopyClasses based.BasedSections C.coneNullMaps :=
  theta based C.coneNullMaps hexact hω
    (C.range_restriction_eq_coneNullMaps_of_exact
      ωCone hconeExact hconeZero)

/-- Representative formula (4.14) for the cone-derived comparison. -/
@[simp]
theorem thetaFromConeCriterion_obstruction
    (based : BasedRowData A i ρ)
    (C : ConeCriterionData based.basedRestriction ρCone)
    (hexact : Function.Exact ρ ω)
    (hω : Function.Surjective ω)
    (ωCone : ConeMaps →ₗ[ℤ] QCone)
    (hconeExact : Function.Exact ρCone ωCone)
    (hconeZero : ∀ x : QCone, x = 0)
    (f : based.BasedSections) :
    thetaFromConeCriterion based C hexact hω
        ωCone hconeExact hconeZero
        (based.basedObstruction ω f) =
      C.coneNullMaps.mkQ f := by
  exact theta_obstruction based C.coneNullMaps hexact hω
    (C.range_restriction_eq_coneNullMaps_of_exact
      ωCone hconeExact hconeZero) f

end ThetaFromCone

end GeneralSphereT.Section4
