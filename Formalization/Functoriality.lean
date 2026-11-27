import Formalization.PathAlgebra

set_option linter.style.header false

/-!
# Functoriality of distributions, paths, and their boundary

The general theorem in this file is the naturality of `boundary` under a
commuting square of additive maps.  Its main specialization is the paper's
identity `d_* ∂ = ∂ d_*`.
-/

noncomputable section

namespace GeneralSphereT.PathAlgebra

/-- Push forward a finite integral distribution along an additive map. -/
def mapDist {X Y : Type*} [AddZero X] [AddZero Y]
    (f : X →+ Y) : Dist X →ₗ[ℤ] Dist Y :=
  Finsupp.lmapDomain ℤ ℤ f

@[simp]
theorem mapDist_single {X Y : Type*} [AddZero X] [AddZero Y]
    (f : X →+ Y) (x : X) (n : ℤ) :
    mapDist f (Finsupp.single x n) = Finsupp.single (f x) n := by
  simp [mapDist]

@[simp]
theorem mapDist_bracket {X Y : Type*} [AddCommGroup X] [AddCommGroup Y]
    (f : X →+ Y) (x : X) :
    mapDist f (bracket x) = bracket (f x) := by
  simp only [bracket, map_sub, mapDist_single, map_zero]

/-- Push forward raw path generators along maps of increments and bases. -/
def rawMapPath {I J X Y : Type*}
    [AddZero I] [AddZero J] [AddZero X] [AddZero Y]
    (i : I →+ J) (b : X →+ Y) :
    RawPath I X →ₗ[ℤ] RawPath J Y :=
  Finsupp.lmapDomain ℤ ℤ fun p => (i p.1, b p.2)

@[simp]
theorem rawMapPath_rawEdge {I J X Y : Type*}
    [AddZero I] [AddZero J] [AddZero X] [AddZero Y]
    (i : I →+ J) (b : X →+ Y) (r : I) (x : X) :
    rawMapPath i b (rawEdge r x) = rawEdge (i r) (b x) := by
  simp [rawMapPath, rawEdge]

theorem rawMapPath_zeroIncrement_le {I J X Y : Type*}
    [AddCommGroup I] [AddCommGroup J] [AddZero X] [AddZero Y]
    (i : I →+ J) (b : X →+ Y) :
    zeroIncrement I X ≤ (zeroIncrement J Y).comap (rawMapPath i b) := by
  rw [zeroIncrement, Submodule.span_le]
  rintro _ ⟨x, rfl⟩
  change rawMapPath i b (rawEdge 0 x) ∈ zeroIncrement J Y
  rw [rawMapPath_rawEdge, map_zero]
  exact Submodule.subset_span (Set.mem_range_self (b x))

/-- The induced map on path quotients. -/
def mapPath {I J X Y : Type*} [AddCommGroup I] [AddCommGroup J]
    [AddZero X] [AddZero Y] (i : I →+ J) (b : X →+ Y) :
    Path I X →ₗ[ℤ] Path J Y :=
  (zeroIncrement I X).mapQ (zeroIncrement J Y) (rawMapPath i b)
    (rawMapPath_zeroIncrement_le i b)

@[simp]
theorem mapPath_edge {I J X Y : Type*} [AddCommGroup I] [AddCommGroup J]
    [AddZero X] [AddZero Y] (i : I →+ J) (b : X →+ Y) (r : I) (x : X) :
    mapPath i b (edge r x) = edge (i r) (b x) := by
  simp [mapPath, edge]

variable {I J X Y : Type*}
variable [AddCommGroup I] [AddCommGroup J] [AddCommGroup X] [AddCommGroup Y]

/-- Naturality before passing to the zero-increment quotient. -/
theorem rawBoundary_natural (φ : I →+ X) (ψ : J →+ Y)
    (i : I →+ J) (b : X →+ Y) (h : b.comp φ = ψ.comp i) :
    (mapDist b).comp (rawBoundary φ) =
      (rawBoundary ψ).comp (rawMapPath i b) := by
  ext p
  have hp : b (φ p.1) = ψ (i p.1) :=
    DFunLike.congr_fun h p.1
  simp [rawBoundary, rawMapPath, hp]

/-- Boundary commutes with the path map induced by a commuting square. -/
theorem boundary_natural (φ : I →+ X) (ψ : J →+ Y)
    (i : I →+ J) (b : X →+ Y) (h : b.comp φ = ψ.comp i) :
    (mapDist b).comp (boundary φ) =
      (boundary ψ).comp (mapPath i b) := by
  ext p
  have hp : b (φ p.1) = ψ (i p.1) :=
    DFunLike.congr_fun h p.1
  simp [boundary, mapPath, rawBoundary, rawMapPath, hp]

/-- The primitive boundary used in the paper. -/
abbrev primitiveBoundary (C : Type*) [AddCommGroup C] :
    Path C C →ₗ[ℤ] Dist C :=
  boundary (AddMonoidHom.id C)

/-- The configuration boundary induced by the coboundary map `d`. -/
abbrev configurationBoundary {C B : Type*} [AddCommGroup C] [AddCommGroup B]
    (d : C →+ B) : Path C B →ₗ[ℤ] Dist B :=
  boundary d

/-- The paper's `d_*` on distributions. -/
abbrev mapDDistribution {C B : Type*} [AddCommGroup C] [AddCommGroup B]
    (d : C →+ B) : Dist C →ₗ[ℤ] Dist B :=
  mapDist d

/-- The paper's `d_*` on paths; it changes only the base label. -/
abbrev mapDPath {C B : Type*} [AddCommGroup C] [AddCommGroup B]
    (d : C →+ B) : Path C C →ₗ[ℤ] Path C B :=
  mapPath (AddMonoidHom.id C) d

/-- The paper's identity `d_* ∂ = ∂ d_*`. -/
theorem mapD_boundary {C B : Type*} [AddCommGroup C] [AddCommGroup B]
    (d : C →+ B) :
    (mapDDistribution d).comp (primitiveBoundary C) =
      (configurationBoundary d).comp (mapDPath d) := by
  exact boundary_natural (AddMonoidHom.id C) d (AddMonoidHom.id C) d rfl

/-- Applying `d_*` changes the base label but leaves the increment `r` untouched. -/
@[simp]
theorem mapDPath_edge {C B : Type*} [AddCommGroup C] [AddCommGroup B]
    (d : C →+ B) (r c : C) :
    mapDPath d (edge r c) = edge r (d c) := by
  simp

/-- Even if `d r = 0`, a nonzero increment is not killed by `d_*` on paths. -/
theorem mapDPath_edge_ne_zero {C B : Type*} [AddCommGroup C] [AddCommGroup B]
    (d : C →+ B) {r : C} (hr : r ≠ 0) (c : C) :
    mapDPath d (edge r c) ≠ 0 := by
  rw [mapDPath_edge]
  exact edge_ne_zero hr (d c)

/-- If `d r = 0`, the configuration boundary of an `r`-edge is zero. -/
theorem configurationBoundary_edge_eq_zero_of_mem_ker
    {C B : Type*} [AddCommGroup C] [AddCommGroup B]
    (d : C →+ B) {r : C} (hr : d r = 0) (a : B) :
    configurationBoundary d (edge r a) = 0 := by
  simp [hr]

end GeneralSphereT.PathAlgebra
