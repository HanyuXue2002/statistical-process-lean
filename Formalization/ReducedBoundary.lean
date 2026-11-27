import Formalization.Normalization

set_option linter.style.header false

/-!
# Boundaries with their reduced codomain

The earlier raw formulas take values in `Dist X`.  This file proves that their
coefficient sum is zero, corestricts them to `RedDist X`, and lifts boundary
naturality to these mathematically precise codomains.
-/

noncomputable section

namespace GeneralSphereT.PathAlgebra

variable {I J X Y : Type*}
variable [AddCommGroup I] [AddCommGroup J] [AddCommGroup X] [AddCommGroup Y]

/-- Pushforward preserves the sum of coefficients. -/
theorem augmentation_mapDist (f : X →+ Y) :
    (augmentation Y).comp (mapDist f) = augmentation X := by
  ext x
  simp [augmentation, mapDist]

/-- Pushforward corestricted to augmentation-zero distributions. -/
def mapRedDist (f : X →+ Y) : RedDist X →ₗ[ℤ] RedDist Y :=
  LinearMap.codRestrict (RedDist Y)
    ((mapDist f).comp (RedDist X).subtype) fun z => by
      calc
        augmentation Y (mapDist f z.1) = augmentation X z.1 := by
          exact LinearMap.congr_fun (augmentation_mapDist f) z.1
        _ = 0 := z.2

@[simp]
theorem mapRedDist_coe (f : X →+ Y) (z : RedDist X) :
    ((mapRedDist f z : RedDist Y) : Dist Y) = mapDist f z.1 :=
  rfl

@[simp]
theorem mapRedDist_redBracket (f : X →+ Y) (x : X) :
    mapRedDist f (redBracket x) = redBracket (f x) := by
  apply Subtype.ext
  simp

/-- Raw path boundaries have coefficient sum zero. -/
theorem augmentation_rawBoundary (φ : I →+ X) :
    (augmentation X).comp (rawBoundary φ) = 0 := by
  ext p
  change augmentation X (rawBoundary φ (rawEdge p.1 p.2)) = 0
  rw [rawBoundary_rawEdge]
  simp

/-- Descended path boundaries still have coefficient sum zero. -/
theorem augmentation_boundary (φ : I →+ X) :
    (augmentation X).comp (boundary φ) = 0 := by
  apply LinearMap.ext
  intro p
  refine Submodule.Quotient.induction_on (p := zeroIncrement I X) p ?_
  intro q
  change augmentation X (rawBoundary φ q) = 0
  exact LinearMap.congr_fun (augmentation_rawBoundary φ) q

/-- The paper's path boundary with its correct reduced codomain. -/
def reducedBoundary (φ : I →+ X) : Path I X →ₗ[ℤ] RedDist X :=
  LinearMap.codRestrict (RedDist X) (boundary φ) fun p => by
    change augmentation X (boundary φ p) = 0
    exact LinearMap.congr_fun (augmentation_boundary φ) p

@[simp]
theorem reducedBoundary_coe (φ : I →+ X) (p : Path I X) :
    ((reducedBoundary φ p : RedDist X) : Dist X) = boundary φ p :=
  rfl

@[simp]
theorem reducedBoundary_edge (φ : I →+ X) (r : I) (x : X) :
    reducedBoundary φ (edge r x) =
      redBracket (x + φ r) - redBracket x := by
  apply Subtype.ext
  simp

/-- Reduced boundary is natural under a commuting square. -/
theorem reducedBoundary_natural (φ : I →+ X) (ψ : J →+ Y)
    (i : I →+ J) (b : X →+ Y) (h : b.comp φ = ψ.comp i) :
    (mapRedDist b).comp (reducedBoundary φ) =
      (reducedBoundary ψ).comp (mapPath i b) := by
  apply LinearMap.ext
  intro p
  apply Subtype.ext
  exact LinearMap.congr_fun (boundary_natural φ ψ i b h) p

/-- Primitive boundary with a reduced target. -/
abbrev primitiveReducedBoundary (C : Type*) [AddCommGroup C] :
    Path C C →ₗ[ℤ] RedDist C :=
  reducedBoundary (AddMonoidHom.id C)

/-- Configuration boundary with a reduced target. -/
abbrev configurationReducedBoundary {C B : Type*}
    [AddCommGroup C] [AddCommGroup B] (d : C →+ B) :
    Path C B →ₗ[ℤ] RedDist B :=
  reducedBoundary d

/-- The fully reduced-typed form of the paper's `d_* ∂ = ∂ d_*`. -/
theorem mapRedDist_primitiveReducedBoundary
    {C B : Type*} [AddCommGroup C] [AddCommGroup B] (d : C →+ B) :
    (mapRedDist d).comp (primitiveReducedBoundary C) =
      (configurationReducedBoundary d).comp (mapDPath d) := by
  exact reducedBoundary_natural (AddMonoidHom.id C) d
    (AddMonoidHom.id C) d rfl

end GeneralSphereT.PathAlgebra
