import Formalization.Functoriality

set_option linter.style.header false

/-!
# Reduced distributions and fibrewise path normalization

This file turns the paper's subscript `0` into literal kernels.  In particular,
`NormalizedPath I X` is the kernel of the base-variable augmentation
`[r; x] ↦ ⟨r⟩`.  The target is the actual augmentation-zero subgroup.
-/

noncomputable section

namespace GeneralSphereT.PathAlgebra

/-- Sum of all coefficients of a free distribution. -/
def augmentation (X : Type*) : Dist X →ₗ[ℤ] ℤ :=
  Finsupp.lsum ℤ fun _ : X => LinearMap.id

@[simp]
theorem augmentation_single {X : Type*} (x : X) (n : ℤ) :
    augmentation X (Finsupp.single x n) = n := by
  simp [augmentation]

/-- The augmentation-zero subgroup `\widetilde{ℤ}[X]`. -/
abbrev RedDist (X : Type*) := LinearMap.ker (augmentation X)

variable {I X : Type*} [AddCommGroup I] [AddCommGroup X]

@[simp]
theorem augmentation_bracket (x : X) : augmentation X (bracket x) = 0 := by
  simp [bracket]

/-- The reduced generator `⟨x⟩`, bundled as an element of `RedDist X`. -/
def redBracket (x : X) : RedDist X :=
  ⟨bracket x, augmentation_bracket x⟩

@[simp]
theorem redBracket_coe (x : X) : (redBracket x : Dist X) = bracket x :=
  rfl

@[simp]
theorem redBracket_zero : redBracket (0 : X) = 0 := by
  apply Subtype.ext
  simp

/-- Before quotienting paths, forget the base and retain the reduced increment. -/
def rawBaseAug : RawPath I X →ₗ[ℤ] RedDist I :=
  Finsupp.linearCombination ℤ fun p : I × X => redBracket p.1

omit [AddCommGroup X] in
@[simp]
theorem rawBaseAug_rawEdge (r : I) (x : X) :
    rawBaseAug (I := I) (X := X) (rawEdge r x) = redBracket r := by
  simp [rawBaseAug, rawEdge]

omit [AddCommGroup X] in
/-- Zero-increment generators lie in the kernel of raw base augmentation. -/
theorem zeroIncrement_le_baseAug_ker :
    zeroIncrement I X ≤ LinearMap.ker (rawBaseAug (I := I) (X := X)) := by
  rw [zeroIncrement, Submodule.span_le]
  rintro _ ⟨x, rfl⟩
  change rawBaseAug (I := I) (X := X) (rawEdge (0 : I) x) = 0
  simp

/-- The base-variable augmentation `[r; x] ↦ ⟨r⟩` on path classes. -/
def baseAug : Path I X →ₗ[ℤ] RedDist I :=
  (zeroIncrement I X).liftQ (rawBaseAug (I := I) (X := X))
    zeroIncrement_le_baseAug_ker

omit [AddCommGroup X] in
@[simp]
theorem baseAug_edge (r : I) (x : X) :
    baseAug (I := I) (X := X) (edge r x) = redBracket r := by
  simp [baseAug, edge]

/-- Paths normalized separately in every nonzero-increment fibre. -/
abbrev NormalizedPath (I X : Type*) [AddCommGroup I] [AddCommGroup X] :=
  LinearMap.ker (baseAug (I := I) (X := X))

@[simp]
theorem baseAug_normalizedEdge (r : I) (x : X) :
    baseAug (I := I) (X := X) (normalizedEdge r x) = 0 := by
  simp [normalizedEdge]

/-- The generator `[r; x] - [r; 0]` as a bundled normalized path. -/
def normalizedEdgeBundled (r : I) (x : X) : NormalizedPath I X :=
  ⟨normalizedEdge r x, baseAug_normalizedEdge r x⟩

theorem normalizedEdge_mem (r : I) (x : X) :
    normalizedEdge r x ∈ NormalizedPath I X :=
  baseAug_normalizedEdge r x

/-- Base augmentation is unchanged before quotienting when only the base is mapped. -/
theorem rawBaseAug_rawMapPath_id {Y : Type*} [AddCommGroup Y] (b : X →+ Y) :
    (rawBaseAug (I := I) (X := Y)).comp
        (rawMapPath (AddMonoidHom.id I) b) =
      rawBaseAug (I := I) (X := X) := by
  ext r
  simp [rawBaseAug, rawMapPath]

/-- Base augmentation is unchanged by `mapPath (id, b)`. -/
theorem baseAug_mapPath_id {Y : Type*} [AddCommGroup Y] (b : X →+ Y) :
    (baseAug (I := I) (X := Y)).comp
        (mapPath (AddMonoidHom.id I) b) =
      baseAug (I := I) (X := X) := by
  apply LinearMap.ext
  intro p
  refine Submodule.Quotient.induction_on (p := zeroIncrement I X) p ?_
  intro q
  change rawBaseAug (I := I) (X := Y)
      (rawMapPath (AddMonoidHom.id I) b q) =
    rawBaseAug (I := I) (X := X) q
  exact LinearMap.congr_fun (rawBaseAug_rawMapPath_id (I := I) b) q

/-- The typed paper identity `ε_base^cf ∘ d_*^P = ε_base^pr`. -/
theorem baseAug_mapD {C B : Type*} [AddCommGroup C] [AddCommGroup B]
    (d : C →+ B) :
    (baseAug (I := C) (X := B)).comp (mapDPath d) =
      baseAug (I := C) (X := C) :=
  baseAug_mapPath_id d

/-- A path killed by `mapPath (id, b)` is automatically fibrewise normalized. -/
theorem normalized_of_mapPath_id_eq_zero {Y : Type*} [AddCommGroup Y]
    (b : X →+ Y) (p : Path I X)
    (h : mapPath (AddMonoidHom.id I) b p = 0) :
    p ∈ NormalizedPath I X := by
  change baseAug (I := I) (X := X) p = 0
  simpa [h] using
    (LinearMap.congr_fun (baseAug_mapPath_id (I := I) b) p).symm

/-- The exact implication used after equation (2.11) in the paper. -/
theorem mapD_eq_zero_mem_primitiveNormalized
    {C B : Type*} [AddCommGroup C] [AddCommGroup B]
    (d : C →+ B) (p : Path C C) (h : mapDPath d p = 0) :
    p ∈ NormalizedPath C C :=
  normalized_of_mapPath_id_eq_zero d p h

end GeneralSphereT.PathAlgebra
