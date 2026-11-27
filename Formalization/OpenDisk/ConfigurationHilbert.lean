import Formalization.OpenDisk.ConditionalRange

/-!
# Normalized configuration vectors

The report's fiber sums form an orthonormal family, and their span is precisely
the embedded invariant Hilbert space. The normalization is `|ker d|^(-1/2)`.
-/

noncomputable section

namespace OpenDisk
open BulkPhaseHilbert

variable {C A : Type*} [AddCommGroup C] [AddCommGroup A]
  (d : C →+ A) (rep : A → C) (hrep : ∀ a, d (rep a) = a)

def configurationCoordinatesEquiv : C ≃ d.ker × A where
  toFun v := (fiberDisplacement d rep hrep v, d v)
  invFun za := rep za.2 + za.1
  left_inv v := by change rep (d v) + (v - rep (d v)) = v; abel
  right_inv za := by
    have hz : d za.1 = 0 := za.1.property
    apply Prod.ext
    · apply Subtype.ext
      change rep za.2 + (za.1 : C) - rep (d (rep za.2 + za.1)) = za.1
      rw [map_add, hrep, hz, add_zero]
      abel
    · change d (rep za.2 + za.1) = za.2
      rw [map_add, hrep, hz, add_zero]

variable [Fintype C] [Fintype A] [Fintype d.ker]

/-- The normalized fiber sum is a genuine Hilbert-space linear isometry. -/
def configurationIsometry (β : C → CirclePhase) :
    EuclideanSpace ℂ A →ₗᵢ[ℂ] EuclideanSpace ℂ C :=
  (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
    (configurationCoordinatesEquiv d rep hrep).symm).toLinearIsometry.comp
      (conditionalIsometry circleCharacter (fun za : d.ker × A =>
        β ((configurationCoordinatesEquiv d rep hrep).symm za)))

theorem configurationIsometry_apply (β : C → CirclePhase) (a : EuclideanSpace ℂ A) (v : C) :
    configurationIsometry d rep hrep β a v =
      normalization d.ker * phaseWeight (β v) * a (d v) := by
  change normalization d.ker *
    phaseWeight (β ((configurationCoordinatesEquiv d rep hrep).symm
      (configurationCoordinatesEquiv d rep hrep v))) * a (d v) = _
  rw [Equiv.symm_apply_apply]

theorem configurationIsometry_mem (β : C → CirclePhase) (a : EuclideanSpace ℂ A) :
    (configurationIsometry d rep hrep β a).ofLp ∈ invariantSpace d (phaseDerivative d β) := by
  have hh := ((configurationEquiv d rep hrep β)
    (fun b => normalization d.ker * a b)).property
  convert hh using 1
  funext v
  rw [show (configurationIsometry d rep hrep β a).ofLp v =
    configurationIsometry d rep hrep β a v from rfl, configurationIsometry_apply]
  change normalization d.ker * phaseWeight (β v) * a (d v) =
    phaseWeight (β v) * (normalization d.ker * a (d v))
  ring

/-- The normalized configuration states span the whole literal invariant subspace. -/
theorem configurationIsometry_range_iff (β : C → CirclePhase) (ψ : EuclideanSpace ℂ C) :
    ψ ∈ LinearMap.range (configurationIsometry d rep hrep β).toLinearMap ↔
      ψ.ofLp ∈ invariantSpace d (phaseDerivative d β) := by
  constructor
  · rintro ⟨a, rfl⟩
    exact configurationIsometry_mem d rep hrep β a
  · intro hψ
    let k := (configurationEquiv d rep hrep β).symm ⟨ψ.ofLp, hψ⟩
    let a : EuclideanSpace ℂ A := WithLp.toLp 2 (fun b => (normalization d.ker)⁻¹ * k b)
    refine ⟨a, ?_⟩
    ext v
    change configurationIsometry d rep hrep β a v = ψ v
    rw [configurationIsometry_apply]
    have hv := congrArg (fun f : invariantSpace d (phaseDerivative d β) => f v)
      ((configurationEquiv d rep hrep β).apply_symm_apply ⟨ψ.ofLp, hψ⟩)
    change phaseWeight (β v) * k (d v) = ψ v at hv
    change normalization d.ker * phaseWeight (β v) *
      ((normalization d.ker)⁻¹ * k (d v)) = ψ v
    rw [← hv]
    field_simp [normalization_ne_zero d.ker]

theorem configurationVectors_orthonormal [DecidableEq A] (β : C → CirclePhase) :
    Orthonormal ℂ (fun a : A => configurationIsometry d rep hrep β (EuclideanSpace.single a 1)) :=
  EuclideanSpace.orthonormal_single.comp_linearIsometry (configurationIsometry d rep hrep β)

end OpenDisk
