import Formalization.OperatorCoefficients

set_option linter.style.header false

/-!
# Section 4: normalized paths as finite families of reduced base distributions

The quotient `Path I X` deletes exactly the zero-increment generators.  It is
therefore the direct sum, over nonzero increments `r`, of the free
distribution groups on the base variable.  The base-normalized subgroup cuts
each summand down to its augmentation kernel.

This file proves that statement without tensor products.  Besides the linear
equivalence, the final theorems say that `mapDPath` acts on each increment
fiber by `mapRedDist` and characterize its kernel fiber by fiber.  This is the
form of (4.20) needed by the Section 4 extension argument.
-/

noncomputable section

namespace GeneralSphereT.PathAlgebra

variable {I X : Type*} [AddCommGroup I] [AddCommGroup X]

/-- A complete increment label together with the proof that it survives the
zero-increment quotient. -/
abbrev NonzeroIncrement (I : Type*) [Zero I] := {r : I // r ≠ 0}

/-- A finite family, indexed by nonzero increments, of unrestricted base
distributions. -/
abbrev PathFiberFamily (I X : Type*) [Zero I] :=
  NonzeroIncrement I →₀ Dist X

local instance pathFiberDecidableEq : DecidableEq I := Classical.decEq _

local instance nonzeroIncrementDecidableEq : DecidableEq (NonzeroIncrement I) :=
  Classical.decEq _

/-! ## Every path is the finite sum of its complete-label fibers -/

/-- Before the zero-increment quotient, send a generator to its nonzero
increment fiber. -/
def rawPathFibers : RawPath I X →ₗ[ℤ] PathFiberFamily I X :=
  Finsupp.linearCombination ℤ fun p =>
    if hp : p.1 ≠ 0 then
      Finsupp.single ⟨p.1, hp⟩ (Finsupp.single p.2 1)
    else 0

omit [AddCommGroup X] in
@[simp]
theorem rawPathFibers_rawEdge (r : I) (x : X) :
    rawPathFibers (rawEdge r x) =
      if hr : r ≠ 0 then
        Finsupp.single ⟨r, hr⟩ (Finsupp.single x 1)
      else 0 := by
  classical
  simp [rawPathFibers, rawEdge]

omit [AddCommGroup X] in
/-- Zero-increment relations have no nonzero fiber. -/
theorem zeroIncrement_le_rawPathFibers_ker :
    zeroIncrement I X ≤ LinearMap.ker (rawPathFibers (I := I) (X := X)) := by
  rw [zeroIncrement, Submodule.span_le]
  rintro _ ⟨x, rfl⟩
  change rawPathFibers (I := I) (X := X) (rawEdge 0 x) = 0
  simp

/-- Collect all base distributions of a path, indexed by their complete
nonzero increment labels. -/
def pathFibers : Path I X →ₗ[ℤ] PathFiberFamily I X :=
  (zeroIncrement I X).liftQ rawPathFibers
    zeroIncrement_le_rawPathFibers_ker

omit [AddCommGroup X] in
@[simp]
theorem pathFibers_edge (r : I) (x : X) :
    pathFibers (edge r x) =
      if hr : r ≠ 0 then
        Finsupp.single ⟨r, hr⟩ (Finsupp.single x 1)
      else 0 := by
  classical
  simp [pathFibers, edge]

omit [AddCommGroup X] in
/-- The `r`-entry of `pathFibers` is the pre-existing complete-label
coefficient extractor. -/
theorem pathFibers_apply (p : Path I X) (r : NonzeroIncrement I) :
    pathFibers p r = pathCoefficient r.1 r.2 p := by
  let hmaps :
      (Finsupp.lapply r).comp (pathFibers (I := I) (X := X)) =
        pathCoefficient r.1 r.2 := by
    ext q y
    rcases q with ⟨s, x⟩
    change (pathFibers (edge s x) r) y =
      (pathCoefficient r.1 r.2 (edge s x)) y
    by_cases hsr : s = r.1
    · subst s
      simp [r.2]
    · by_cases hs0 : s = 0
      · subst s
        simp
      · have hsub : (⟨s, hs0⟩ : NonzeroIncrement I) ≠ r := by
          intro h
          exact hsr (congrArg Subtype.val h)
        simp [pathFibers_edge, hs0, hsr, hsub]
  exact LinearMap.congr_fun hmaps p

/-- Reinsert one nonzero increment fiber as a path. -/
def fiberPath (r : NonzeroIncrement I) : Dist X →ₗ[ℤ] Path I X :=
  Finsupp.linearCombination ℤ fun x => edge r.1 x

omit [AddCommGroup X] in
@[simp]
theorem fiberPath_single (r : NonzeroIncrement I) (x : X) (n : ℤ) :
    fiberPath r (Finsupp.single x n) = n • edge r.1 x := by
  simp [fiberPath]

/-- Sum all nonzero increment fibers. -/
def fibersToPath : PathFiberFamily I X →ₗ[ℤ] Path I X :=
  Finsupp.lsum ℤ (fiberPath (I := I) (X := X))

omit [AddCommGroup X] in
@[simp]
theorem fibersToPath_single (r : NonzeroIncrement I) (z : Dist X) :
    fibersToPath (Finsupp.single r z) = fiberPath r z := by
  simp [fibersToPath]

omit [AddCommGroup X] in
@[simp]
theorem pathFibers_fiberPath (r : NonzeroIncrement I) (z : Dist X) :
    pathFibers (fiberPath r z) = Finsupp.single r z := by
  induction z using Finsupp.induction with
  | zero => simp [fiberPath]
  | single_add x n z hx hz ih =>
      rw [map_add, map_add, ih]
      simp [fiberPath, r.2]

omit [AddCommGroup X] in
@[simp]
theorem pathFibers_fibersToPath (f : PathFiberFamily I X) :
    pathFibers (fibersToPath f) = f := by
  induction f using Finsupp.induction with
  | zero => simp [fibersToPath]
  | single_add r z f hr hf ih =>
      rw [map_add, map_add, ih]
      simp

omit [AddCommGroup X] in
@[simp]
theorem fibersToPath_pathFibers (p : Path I X) :
    fibersToPath (pathFibers p) = p := by
  let hmaps :
      (fibersToPath (I := I) (X := X)).comp pathFibers =
        LinearMap.id := by
    ext q
    rcases q with ⟨r, x⟩
    change fibersToPath (pathFibers (edge r x)) = edge r x
    by_cases hr0 : r = 0
    · subst r
      simp
    · simp [pathFibers_edge, hr0, fiberPath]
  exact LinearMap.congr_fun hmaps p

/-- The zero-increment quotient is exactly the finite direct sum of its
nonzero complete-label base-distribution fibers. -/
def pathFiberLinearEquiv :
    Path I X ≃ₗ[ℤ] PathFiberFamily I X where
  toLinearMap := pathFibers
  invFun := fibersToPath
  left_inv := fibersToPath_pathFibers
  right_inv := pathFibers_fibersToPath

/-! ## Base normalization is fiberwise augmentation zero -/

omit [AddCommGroup X] in
/-- The augmentation of one complete-label coefficient distribution is the
corresponding nonzero coordinate of the path's base augmentation. -/
theorem augmentation_pathCoefficient
    (r : I) (hr : r ≠ 0) (p : Path I X) :
    augmentation X (pathCoefficient r hr p) =
      ((baseAug p : RedDist I) : Dist I) r := by
  let hmaps :
      (augmentation X).comp (pathCoefficient r hr) =
        (Finsupp.lapply r).comp
          ((RedDist I).subtype.comp (baseAug (I := I) (X := X))) := by
    ext q
    rcases q with ⟨s, x⟩
    change augmentation X (pathCoefficient r hr (edge s x)) =
      ((baseAug (edge s x) : RedDist I) : Dist I) r
    by_cases hsr : s = r
    · subst s
      simp [bracket, hr]
    · by_cases hs0 : s = 0
      · subst s
        simp
      · simp [bracket, hsr, hr]
  exact LinearMap.congr_fun hmaps p

/-- Finite nonzero-increment families whose base distribution in every fiber
has augmentation zero.  This is a concrete finite-support family of
`RedDist X` values, with the subtype condition left pointwise for convenient
calculation. -/
def NormalizedFiberFamily (I X : Type*) [AddCommGroup I] [AddCommGroup X] :
    Submodule ℤ (PathFiberFamily I X) where
  carrier := {f | ∀ r, augmentation X (f r) = 0}
  zero_mem' := by intro r; simp
  add_mem' := by
    intro f g hf hg r
    simp [hf r, hg r]
  smul_mem' := by
    intro n f hf r
    simp [hf r]

@[simp]
theorem mem_normalizedFiberFamily_iff (f : PathFiberFamily I X) :
    f ∈ NormalizedFiberFamily I X ↔
      ∀ r, augmentation X (f r) = 0 :=
  Iff.rfl

/-- A normalized path gives a finite family of reduced base distributions. -/
def normalizedPathToFiberFamily :
    NormalizedPath I X →ₗ[ℤ] NormalizedFiberFamily I X :=
  LinearMap.codRestrict (NormalizedFiberFamily I X)
    ((pathFibers (I := I) (X := X)).comp (NormalizedPath I X).subtype)
    fun p r => by
      change augmentation X (pathFibers p.1 r) = 0
      rw [pathFibers_apply, augmentation_pathCoefficient]
      simp

omit [AddCommGroup X] in
/-- The base augmentation of one reinserted fiber only records the total
coefficient of its base distribution. -/
theorem baseAug_fiberPath (r : NonzeroIncrement I) (z : Dist X) :
    baseAug (fiberPath r z) = augmentation X z • redBracket r.1 := by
  induction z using Finsupp.induction with
  | zero => simp [fiberPath]
  | single_add x n z hx hz ih =>
      rw [map_add, map_add, ih]
      simp [fiberPath, add_smul]

omit [AddCommGroup X] in
/-- Reassembling pointwise reduced fibers produces a normalized path. -/
theorem baseAug_fibersToPath_eq_zero
    (f : PathFiberFamily I X)
    (hf : ∀ r, augmentation X (f r) = 0) :
    baseAug (fibersToPath f) = 0 := by
  classical
  rw [fibersToPath, Finsupp.lsum_apply, map_finsuppSum]
  simp [baseAug_fiberPath, Finsupp.sum, hf]

/-- Reassemble a normalized fiber family as a bundled normalized path. -/
def normalizedFiberFamilyToPath :
    NormalizedFiberFamily I X →ₗ[ℤ] NormalizedPath I X :=
  LinearMap.codRestrict (NormalizedPath I X)
    ((fibersToPath (I := I) (X := X)).comp
      (NormalizedFiberFamily I X).subtype)
    fun f => baseAug_fibersToPath_eq_zero f.1 f.2

@[simp]
theorem normalizedPathToFiberFamily_inverse
    (f : NormalizedFiberFamily I X) :
    normalizedPathToFiberFamily (normalizedFiberFamilyToPath f) = f := by
  apply Subtype.ext
  exact pathFibers_fibersToPath f.1

@[simp]
theorem normalizedFiberFamilyToPath_inverse
    (p : NormalizedPath I X) :
    normalizedFiberFamilyToPath (normalizedPathToFiberFamily p) = p := by
  apply Subtype.ext
  exact fibersToPath_pathFibers p.1

/-- Tensor-free form of
`NormalizedPath I X ≃ ⊕ (r ≠ 0), RedDist X`. -/
def normalizedPathFiberLinearEquiv :
    NormalizedPath I X ≃ₗ[ℤ] NormalizedFiberFamily I X where
  toLinearMap := normalizedPathToFiberFamily
  invFun := normalizedFiberFamilyToPath
  left_inv := normalizedFiberFamilyToPath_inverse
  right_inv := normalizedPathToFiberFamily_inverse

/-! ## `d_*` acts independently on every fiber -/

/-- `mapDPath` restricted to normalized paths. -/
def mapDNormalizedPath {C B : Type*} [AddCommGroup C] [AddCommGroup B]
    (d : C →+ B) : NormalizedPath C C →ₗ[ℤ] NormalizedPath C B :=
  LinearMap.codRestrict (NormalizedPath C B)
    ((mapDPath d).comp (NormalizedPath C C).subtype)
    fun p => by
      change baseAug (mapDPath d p.1) = 0
      have h := LinearMap.congr_fun (baseAug_mapD d) p.1
      simpa [p.2] using h

@[simp]
theorem mapDNormalizedPath_coe
    {C B : Type*} [AddCommGroup C] [AddCommGroup B]
    (d : C →+ B) (p : NormalizedPath C C) :
    (mapDNormalizedPath d p : Path C B) = mapDPath d p.1 :=
  rfl

/-- On every complete nonzero increment fiber, `mapDPath` is exactly
`mapRedDist` on the base distribution. -/
theorem normalizedPathToFiberFamily_mapD_apply
    {C B : Type*} [AddCommGroup C] [AddCommGroup B]
    (d : C →+ B) (p : NormalizedPath C C)
    (r : NonzeroIncrement C) :
    ((normalizedPathToFiberFamily (mapDNormalizedPath d p) :
        NormalizedFiberFamily C B) : PathFiberFamily C B) r =
      mapDist d
        (((normalizedPathToFiberFamily p : NormalizedFiberFamily C C) :
          PathFiberFamily C C) r) := by
  rw [show
      (((normalizedPathToFiberFamily (mapDNormalizedPath d p) :
          NormalizedFiberFamily C B) : PathFiberFamily C B) r) =
        pathCoefficient r.1 r.2 (mapDPath d p.1) by
      exact pathFibers_apply _ _]
  rw [pathCoefficient_mapDPath]
  congr 1
  symm
  exact pathFibers_apply p.1 r

/-- The actual reduced distribution carried by one nonzero increment fiber of
a normalized path. -/
def normalizedFiber (p : NormalizedPath I X) (r : NonzeroIncrement I) :
    RedDist X :=
  ⟨((normalizedPathToFiberFamily p : NormalizedFiberFamily I X).1 r),
    (normalizedPathToFiberFamily p).2 r⟩

@[simp]
theorem normalizedFiber_zero (r : NonzeroIncrement I) :
    normalizedFiber (0 : NormalizedPath I X) r = 0 := by
  apply Subtype.ext
  simp [normalizedFiber]

/-- Bundled fiberwise form of `normalizedPathToFiberFamily_mapD_apply`:
`mapDPath` applies `mapRedDist` independently at every nonzero increment. -/
theorem normalizedFiber_mapD
    {C B : Type*} [AddCommGroup C] [AddCommGroup B]
    (d : C →+ B) (p : NormalizedPath C C)
    (r : NonzeroIncrement C) :
    normalizedFiber (mapDNormalizedPath d p) r =
      mapRedDist d (normalizedFiber p r) := by
  apply Subtype.ext
  exact normalizedPathToFiberFamily_mapD_apply d p r

/-- Kernel criterion replacing the tensor-product kernel calculation in
(4.20): a normalized path is killed by `d_*` exactly when every nonzero
increment fiber is killed by the induced map on reduced base distributions. -/
theorem mapDNormalizedPath_eq_zero_iff
    {C B : Type*} [AddCommGroup C] [AddCommGroup B]
    (d : C →+ B) (p : NormalizedPath C C) :
    mapDNormalizedPath d p = 0 ↔
      ∀ r : NonzeroIncrement C,
        mapRedDist d (normalizedFiber p r) = 0 := by
  constructor
  · intro hp r
    have hfiber := congrArg (fun q : NormalizedPath C B => normalizedFiber q r) hp
    rw [normalizedFiber_mapD] at hfiber
    simpa using hfiber
  · intro hf
    apply Subtype.ext
    apply (pathFiberLinearEquiv (I := C) (X := B)).injective
    ext r x
    change (pathFibers (mapDPath d p.1) r) x = 0
    rw [pathFibers_apply, pathCoefficient_mapDPath,
      ← pathFibers_apply p.1 r]
    have hcoe := congrArg Subtype.val (hf r)
    exact DFunLike.congr_fun hcoe x

/-! ## The kernel as a finite family of primitive-relation fibers -/

/-- One reduced base distribution extracted from a normalized fiber family. -/
def normalizedFamilyFiber
    (f : NormalizedFiberFamily I X) (r : NonzeroIncrement I) : RedDist X :=
  ⟨f.1 r, f.2 r⟩

@[simp]
theorem normalizedFamilyFiber_zero (r : NonzeroIncrement I) :
    normalizedFamilyFiber (0 : NormalizedFiberFamily I X) r = 0 := by
  apply Subtype.ext
  simp [normalizedFamilyFiber]

@[simp]
theorem normalizedFamilyFiber_add
    (f g : NormalizedFiberFamily I X) (r : NonzeroIncrement I) :
    normalizedFamilyFiber (f + g) r =
      normalizedFamilyFiber f r + normalizedFamilyFiber g r := by
  apply Subtype.ext
  rfl

@[simp]
theorem normalizedFamilyFiber_smul
    (n : ℤ) (f : NormalizedFiberFamily I X) (r : NonzeroIncrement I) :
    normalizedFamilyFiber (n • f) r = n • normalizedFamilyFiber f r := by
  apply Subtype.ext
  rfl

/-- Reassembly does not change any reduced fiber. -/
@[simp]
theorem normalizedFiber_normalizedFiberFamilyToPath
    (f : NormalizedFiberFamily I X) (r : NonzeroIncrement I) :
    normalizedFiber (normalizedFiberFamilyToPath f) r =
      normalizedFamilyFiber f r := by
  have h := congrArg (fun g : NormalizedFiberFamily I X =>
    normalizedFamilyFiber g r) (normalizedPathToFiberFamily_inverse f)
  exact h

/-- Fiber families for which every base distribution is a primitive
relation.  This is the tensor-free right-hand side of (4.20). -/
def RelationFiberFamily
    {C B : Type*} [AddCommGroup C] [AddCommGroup B]
    (d : C →+ B) : Submodule ℤ (NormalizedFiberFamily C C) where
  carrier := {f | ∀ r : NonzeroIncrement C,
    mapRedDist d (normalizedFamilyFiber f r) = 0}
  zero_mem' := by intro r; simp
  add_mem' := by
    intro f g hf hg r
    rw [normalizedFamilyFiber_add, map_add, hf r, hg r, add_zero]
  smul_mem' := by
    intro n f hf r
    rw [normalizedFamilyFiber_smul, map_smul, hf r, smul_zero]

@[simp]
theorem mem_relationFiberFamily_iff
    {C B : Type*} [AddCommGroup C] [AddCommGroup B]
    (d : C →+ B) (f : NormalizedFiberFamily C C) :
    f ∈ RelationFiberFamily d ↔
      ∀ r : NonzeroIncrement C,
        mapRedDist d (normalizedFamilyFiber f r) = 0 :=
  Iff.rfl

/-- Pass from a normalized relation path to its family of primitive-relation
fibers. -/
def relationPathToFiberFamily
    {C B : Type*} [AddCommGroup C] [AddCommGroup B]
    (d : C →+ B) :
    LinearMap.ker (mapDNormalizedPath d) →ₗ[ℤ] RelationFiberFamily d :=
  LinearMap.codRestrict (RelationFiberFamily d)
    ((normalizedPathToFiberFamily (I := C) (X := C)).comp
      (LinearMap.ker (mapDNormalizedPath d)).subtype) fun p r => by
        exact (mapDNormalizedPath_eq_zero_iff d p.1).1 p.2 r

/-- Reassemble a family of primitive-relation fibers as a normalized relation
path. -/
def relationFiberFamilyToPath
    {C B : Type*} [AddCommGroup C] [AddCommGroup B]
    (d : C →+ B) :
    RelationFiberFamily d →ₗ[ℤ] LinearMap.ker (mapDNormalizedPath d) :=
  LinearMap.codRestrict (LinearMap.ker (mapDNormalizedPath d))
    ((normalizedFiberFamilyToPath (I := C) (X := C)).comp
      (RelationFiberFamily d).subtype) fun f => by
        rw [LinearMap.mem_ker]
        apply (mapDNormalizedPath_eq_zero_iff d _).2
        intro r
        change mapRedDist d
          (normalizedFiber (normalizedFiberFamilyToPath f.1) r) = 0
        rw [normalizedFiber_normalizedFiberFamilyToPath]
        exact f.2 r

/-- Exact tensor-free version of (4.20): the kernel of `d_*` on normalized
paths is linearly equivalent to the finite family of its primitive-relation
fibers. -/
def relationPathFiberLinearEquiv
    {C B : Type*} [AddCommGroup C] [AddCommGroup B]
    (d : C →+ B) :
    LinearMap.ker (mapDNormalizedPath d) ≃ₗ[ℤ] RelationFiberFamily d where
  toLinearMap := relationPathToFiberFamily d
  invFun := relationFiberFamilyToPath d
  left_inv := by
    intro p
    apply Subtype.ext
    exact normalizedFiberFamilyToPath_inverse p.1
  right_inv := by
    intro f
    apply Subtype.ext
    exact normalizedPathToFiberFamily_inverse f.1

end GeneralSphereT.PathAlgebra
