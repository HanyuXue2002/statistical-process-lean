import Formalization.Cells
import Formalization.CoordinateRestriction

set_option linter.style.header false

/-!
# Explicit primitive two-cell chains

This file replaces an abstract degree-two chain group by the free integral
module on the two primitive cell shapes used in (2.26):

* an oriented transverse square, tagged by `(i,j,g,h)` with `i ≠ j`;
* a same-coordinate triangle, tagged by `(i,g,h)`.

The base configuration is deliberately kept outside the tag.  Thus, for every
complete oriented cell type, its coefficients can be collected as an honest
distribution of bases.  No contracting homotopy, and in particular no map
called `H`, is constructed here.
-/

noncomputable section

namespace GeneralSphereT.PathAlgebra

/--
The complete oriented type of a primitive two-cell.  The proof field in the
square constructor records that the two coordinates are genuinely transverse;
proof irrelevance ensures that it adds no spurious distinction between tags.
-/
inductive PrimitiveCellType (ι G : Type*) where
  | transverseSquare (i j : ι) (hij : i ≠ j) (g h : G)
  | sameCoordinateTriangle (i : ι) (g h : G)

/-- A primitive two-cell is its complete oriented type together with its base. -/
abbrev PrimitiveCellData (ι G : Type*) [Zero G] :=
  PrimitiveCellType ι G × Configuration ι G

/-- The free integral module on the explicit primitive two-cells. -/
abbrev PrimitiveCellChain₂ (ι G : Type*) [Zero G] :=
  PrimitiveCellData ι G →₀ ℤ

/-- The basis two-cell with tag `τ` and base `c`. -/
def primitiveCellGenerator {ι G : Type*} [Zero G]
    (τ : PrimitiveCellType ι G) (c : Configuration ι G) :
    PrimitiveCellChain₂ ι G :=
  Finsupp.single (τ, c) 1

section Boundary

variable {ι G : Type*} [AddCommGroup G]

/-- The path boundary of one explicitly tagged primitive two-cell. -/
def primitiveCellBoundaryGenerator :
    PrimitiveCellData ι G →
      Path (Configuration ι G) (Configuration ι G)
  | (.transverseSquare i j _ g h, c) =>
      square (AddMonoidHom.id (Configuration ι G))
        (Finsupp.single i g) (Finsupp.single j h) c
  | (.sameCoordinateTriangle i g h, c) =>
      triangle (AddMonoidHom.id (Configuration ι G))
        (Finsupp.single i g) (Finsupp.single i h) c

/-- The linear degree-two boundary into primitive paths. -/
def primitiveCellBoundary₂ :
    PrimitiveCellChain₂ ι G →ₗ[ℤ]
      Path (Configuration ι G) (Configuration ι G) :=
  Finsupp.linearCombination ℤ primitiveCellBoundaryGenerator

@[simp]
theorem primitiveCellBoundary₂_single
    (τ : PrimitiveCellType ι G) (c : Configuration ι G) (n : ℤ) :
    primitiveCellBoundary₂ (Finsupp.single (τ, c) n) =
      n • primitiveCellBoundaryGenerator (τ, c) := by
  simp [primitiveCellBoundary₂]

@[simp]
theorem primitiveCellBoundary₂_single_data
    (cell : PrimitiveCellData ι G) (n : ℤ) :
    primitiveCellBoundary₂ (Finsupp.single cell n) =
      n • primitiveCellBoundaryGenerator cell := by
  rcases cell with ⟨τ, c⟩
  exact primitiveCellBoundary₂_single τ c n

@[simp]
theorem primitiveCellBoundary₂_primitiveCellGenerator
    (τ : PrimitiveCellType ι G) (c : Configuration ι G) :
    primitiveCellBoundary₂ (primitiveCellGenerator τ c) =
      primitiveCellBoundaryGenerator (τ, c) := by
  simp [primitiveCellGenerator]

/-- Every explicit primitive two-cell has boundary of boundary zero. -/
@[simp]
theorem primitiveBoundary_primitiveCellBoundaryGenerator
    (cell : PrimitiveCellData ι G) :
    primitiveBoundary (Configuration ι G)
        (primitiveCellBoundaryGenerator cell) = 0 := by
  rcases cell with ⟨τ, c⟩
  cases τ with
  | transverseSquare i j hij g h =>
      exact boundary_square _ _ _ _
  | sameCoordinateTriangle i g h =>
      exact boundary_triangle _ _ _ _

/-- Boundary squared is zero on every primitive two-chain. -/
@[simp]
theorem primitiveBoundary_primitiveCellBoundary₂
    (z : PrimitiveCellChain₂ ι G) :
    primitiveBoundary (Configuration ι G) (primitiveCellBoundary₂ z) = 0 := by
  classical
  induction z using Finsupp.induction with
  | zero => simp
  | single_add cell n z _ _ ih =>
      rw [map_add, map_add, ih, primitiveCellBoundary₂_single, map_smul,
        primitiveBoundary_primitiveCellBoundaryGenerator, smul_zero, zero_add]

/-- Linear-map form of the chain-complex identity `∂₁ ∘ ∂₂ = 0`. -/
theorem primitiveBoundary_comp_primitiveCellBoundary₂ :
    (primitiveBoundary (Configuration ι G)).comp primitiveCellBoundary₂ =
      (0 : PrimitiveCellChain₂ ι G →ₗ[ℤ]
        Dist (Configuration ι G)) := by
  apply LinearMap.ext
  intro z
  simp

end Boundary

section CompleteTypeCoefficients

variable {ι G : Type*} [Zero G]

local instance instDecidableEqPrimitiveCellType :
    DecidableEq (PrimitiveCellType ι G) := Classical.decEq _

/--
For a fixed complete oriented cell type `τ`, collect the coefficients of
all cells of type `τ` as a distribution of their base configurations.
-/
def primitiveCellTypeCoefficient (τ : PrimitiveCellType ι G) :
    PrimitiveCellChain₂ ι G →ₗ[ℤ] Dist (Configuration ι G) := by
  classical
  exact Finsupp.linearCombination ℤ fun cell =>
    if cell.1 = τ then Finsupp.single cell.2 1 else 0

@[simp]
theorem primitiveCellTypeCoefficient_single
    (τ σ : PrimitiveCellType ι G) (c : Configuration ι G) (n : ℤ) :
    primitiveCellTypeCoefficient τ (Finsupp.single (σ, c) n) =
      if σ = τ then Finsupp.single c n else 0 := by
  classical
  by_cases hστ : σ = τ <;>
    simp [primitiveCellTypeCoefficient, hστ]

@[simp]
theorem primitiveCellTypeCoefficient_primitiveCellGenerator
    (τ σ : PrimitiveCellType ι G) (c : Configuration ι G) :
    primitiveCellTypeCoefficient τ (primitiveCellGenerator σ c) =
      if σ = τ then Finsupp.single c 1 else 0 := by
  simp [primitiveCellGenerator]

/-- Evaluating the collected distribution recovers the original cell entry. -/
theorem primitiveCellTypeCoefficient_apply
    (τ : PrimitiveCellType ι G) (z : PrimitiveCellChain₂ ι G)
    (c : Configuration ι G) :
    primitiveCellTypeCoefficient τ z c = z (τ, c) := by
  classical
  induction z using Finsupp.induction with
  | zero => simp
  | single_add cell n z hcell hz ih =>
      rcases cell with ⟨σ, b⟩
      simp only [map_add, primitiveCellTypeCoefficient_single,
        Finsupp.add_apply, ih]
      by_cases hστ : σ = τ
      · subst σ
        simp [Finsupp.single_apply]
      · have hpair : (σ, b) ≠ (τ, c) := by
          intro h
          exact hστ (congrArg Prod.fst h)
        simp [hστ, hpair]

/-- A two-chain is determined by all complete-type coefficient distributions. -/
theorem primitiveCellChain₂_ext
    {z w : PrimitiveCellChain₂ ι G}
    (h : ∀ τ, primitiveCellTypeCoefficient τ z =
      primitiveCellTypeCoefficient τ w) :
    z = w := by
  classical
  ext cell
  rcases cell with ⟨τ, c⟩
  have hτ := congrArg (fun u : Dist (Configuration ι G) => u c) (h τ)
  simpa [primitiveCellTypeCoefficient_apply] using hτ

end CompleteTypeCoefficients

section CoordinateRestriction

variable {ι G : Type*} [LinearOrder ι] [AddCommGroup G]

local instance instDecidablePrimitiveCellMembership (S : Set ι) :
    DecidablePred (fun i => i ∈ S) := Classical.decPred _

/--
Restriction of one primitive two-cell.  A cell is sent to zero if one of its
tagged coordinates is deleted; otherwise it becomes the corresponding cell
on the inherited-order subtype.  Its base is always restricted literally.
-/
def restrictPrimitiveCellGenerator (S : Set ι) :
    PrimitiveCellData ι G → PrimitiveCellChain₂ S G
  | (.transverseSquare i j hij g h, c) =>
      if hi : i ∈ S then
        if hj : j ∈ S then
          primitiveCellGenerator
            (.transverseSquare ⟨i, hi⟩ ⟨j, hj⟩
              (fun hsub => hij (congrArg Subtype.val hsub)) g h)
            (coordinateRestriction S c)
        else 0
      else 0
  | (.sameCoordinateTriangle i g h, c) =>
      if hi : i ∈ S then
        primitiveCellGenerator (.sameCoordinateTriangle ⟨i, hi⟩ g h)
          (coordinateRestriction S c)
      else 0

/-- Coordinate restriction extended linearly to primitive two-chains. -/
def restrictPrimitiveCellChain₂ (S : Set ι) :
    PrimitiveCellChain₂ ι G →ₗ[ℤ] PrimitiveCellChain₂ S G :=
  Finsupp.linearCombination ℤ (restrictPrimitiveCellGenerator S)

omit [LinearOrder ι] in
@[simp]
theorem restrictPrimitiveCellChain₂_single
    (S : Set ι) (cell : PrimitiveCellData ι G) (n : ℤ) :
    restrictPrimitiveCellChain₂ S (Finsupp.single cell n) =
      n • restrictPrimitiveCellGenerator S cell := by
  simp [restrictPrimitiveCellChain₂]

/--
Generator-level restriction naturality.  The deleted-coordinate cases reduce
to `square_zero_left`, `square_zero_right`, or a triangle all of whose labels
restrict to zero.
-/
theorem primitiveCellBoundary₂_restrictPrimitiveCellGenerator
    (S : Set ι) (cell : PrimitiveCellData ι G) :
    primitiveCellBoundary₂ (restrictPrimitiveCellGenerator S cell) =
      mapPath (coordinateRestriction S) (coordinateRestriction S)
        (primitiveCellBoundaryGenerator cell) := by
  classical
  rcases cell with ⟨τ, c⟩
  cases τ with
  | transverseSquare i j hij g h =>
      by_cases hi : i ∈ S <;> by_cases hj : j ∈ S <;>
        simp [restrictPrimitiveCellGenerator, hi, hj, primitiveCellGenerator,
          primitiveCellBoundaryGenerator, square]
  | sameCoordinateTriangle i g h =>
      by_cases hi : i ∈ S <;>
        simp [restrictPrimitiveCellGenerator, hi, primitiveCellGenerator,
          primitiveCellBoundaryGenerator, triangle]

/-- The explicit degree-two boundary strictly commutes with restriction. -/
theorem primitiveCellBoundary₂_restrictPrimitiveCellChain₂
    (S : Set ι) (z : PrimitiveCellChain₂ ι G) :
    primitiveCellBoundary₂ (restrictPrimitiveCellChain₂ S z) =
      mapPath (coordinateRestriction S) (coordinateRestriction S)
        (primitiveCellBoundary₂ z) := by
  classical
  induction z using Finsupp.induction with
  | zero => simp
  | single_add cell n z _ _ ih =>
      simp only [map_add, restrictPrimitiveCellChain₂_single,
        primitiveCellBoundary₂_single_data, map_smul, ih]
      rw [primitiveCellBoundary₂_restrictPrimitiveCellGenerator]

/-- Linear-map form of strict degree-two restriction naturality. -/
theorem primitiveCellBoundary₂_comp_restrictPrimitiveCellChain₂
    (S : Set ι) :
    (primitiveCellBoundary₂ (ι := S) (G := G)).comp
        (restrictPrimitiveCellChain₂ S) =
      (mapPath (coordinateRestriction S) (coordinateRestriction S)).comp
        (primitiveCellBoundary₂ (ι := ι) (G := G)) := by
  apply LinearMap.ext
  intro z
  exact primitiveCellBoundary₂_restrictPrimitiveCellChain₂ S z

end CoordinateRestriction

end GeneralSphereT.PathAlgebra
