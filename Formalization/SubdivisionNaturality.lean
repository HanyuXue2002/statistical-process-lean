import Formalization.Subdivision

set_option linter.style.header false

/-!
# Naturality of ordered subdivision

This file packages the physical version of ordered subdivision: the increment is
still a finitely supported configuration, while the base point moves through an
arbitrary additive image of that configuration.  It then proves the two
naturality identities used in (2.14).
-/

noncomputable section

namespace GeneralSphereT.PathAlgebra

section SubdivisionAlong

variable {ι G X : Type*} [LinearOrder ι] [AddCommGroup G] [AddCommGroup X]

/-- Extend ordered subdivision along `φ` linearly before taking the path quotient. -/
def rawSubdivisionAlong (φ : Configuration ι G →+ X) :
    RawPath (Configuration ι G) X →ₗ[ℤ] Path (Configuration ι G) X :=
  Finsupp.linearCombination ℤ fun p => orderedPathAlong φ p.1 p.2

@[simp]
theorem rawSubdivisionAlong_rawEdge (φ : Configuration ι G →+ X)
    (r : Configuration ι G) (x : X) :
    rawSubdivisionAlong φ (rawEdge r x) = orderedPathAlong φ r x := by
  simp [rawSubdivisionAlong, rawEdge]

/-- Subdivision along `φ` kills every zero-increment relation. -/
theorem zeroIncrement_le_rawSubdivisionAlong_ker
    (φ : Configuration ι G →+ X) :
    zeroIncrement (Configuration ι G) X ≤
      LinearMap.ker (rawSubdivisionAlong φ) := by
  refine (Submodule.span_le).2 ?_
  rintro _ ⟨x, rfl⟩
  change rawSubdivisionAlong φ (rawEdge 0 x) = 0
  simp [orderedPathAlong]

/-- Coordinatewise subdivision of paths whose base moves along `φ`. -/
def subdivisionAlong (φ : Configuration ι G →+ X) :
    Path (Configuration ι G) X →ₗ[ℤ] Path (Configuration ι G) X :=
  (zeroIncrement (Configuration ι G) X).liftQ
    (rawSubdivisionAlong φ) (zeroIncrement_le_rawSubdivisionAlong_ker φ)

@[simp]
theorem subdivisionAlong_edge (φ : Configuration ι G →+ X)
    (r : Configuration ι G) (x : X) :
    subdivisionAlong φ (edge r x) = orderedPathAlong φ r x := by
  simp [subdivisionAlong, edge]

/-- Before quotienting, subdivision along `φ` preserves `φ`-boundary. -/
theorem boundary_rawSubdivisionAlong (φ : Configuration ι G →+ X) :
    (boundary φ).comp (rawSubdivisionAlong φ) = rawBoundary φ := by
  ext p
  simp [rawSubdivisionAlong, rawBoundary, boundary_orderedPathAlong]

/-- Subdivision along `φ` preserves the boundary. -/
theorem boundary_subdivisionAlong (φ : Configuration ι G →+ X) :
    (boundary φ).comp (subdivisionAlong φ) = boundary φ := by
  apply LinearMap.ext
  intro p
  refine Submodule.Quotient.induction_on
    (p := zeroIncrement (Configuration ι G) X) p ?_
  intro raw
  change boundary φ (rawSubdivisionAlong φ raw) = rawBoundary φ raw
  exact LinearMap.congr_fun (boundary_rawSubdivisionAlong φ) raw

/-- At the identity map, raw subdivision along a map is primitive subdivision. -/
theorem rawSubdivisionAlong_id :
    rawSubdivisionAlong (AddMonoidHom.id (Configuration ι G)) = rawSubdivision := by
  ext p
  simp [rawSubdivisionAlong, rawSubdivision, orderedPathAlong_id]

/-- At the identity map, subdivision along a map is primitive subdivision. -/
theorem subdivisionAlong_id :
    subdivisionAlong (AddMonoidHom.id (Configuration ι G)) = subdivision := by
  apply LinearMap.ext
  intro p
  refine Submodule.Quotient.induction_on
    (p := zeroIncrement (Configuration ι G) (Configuration ι G)) p ?_
  intro raw
  change rawSubdivisionAlong (AddMonoidHom.id (Configuration ι G)) raw =
    rawSubdivision raw
  exact LinearMap.congr_fun rawSubdivisionAlong_id raw

/-- The raw form of compatibility between subdivision and `d_*`. -/
theorem mapDPath_rawSubdivision {B : Type*} [AddCommGroup B]
    (d : Configuration ι G →+ B) :
    (mapDPath d).comp rawSubdivision =
      (rawSubdivisionAlong d).comp
        (rawMapPath (AddMonoidHom.id (Configuration ι G)) d) := by
  ext p
  simp [rawSubdivision, rawSubdivisionAlong, rawMapPath,
    mapDPath_orderedPath]

/-- Applying `d_*` commutes with ordered subdivision. -/
theorem mapDPath_subdivision {B : Type*} [AddCommGroup B]
    (d : Configuration ι G →+ B) :
    (mapDPath d).comp subdivision =
      (subdivisionAlong d).comp (mapDPath d) := by
  apply LinearMap.ext
  intro p
  refine Submodule.Quotient.induction_on
    (p := zeroIncrement (Configuration ι G) (Configuration ι G)) p ?_
  intro raw
  change mapDPath d (rawSubdivision raw) =
    rawSubdivisionAlong d
      (rawMapPath (AddMonoidHom.id (Configuration ι G)) d raw)
  exact LinearMap.congr_fun (mapDPath_rawSubdivision d) raw

end SubdivisionAlong

end GeneralSphereT.PathAlgebra
