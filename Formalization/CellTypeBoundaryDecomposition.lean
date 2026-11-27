import Formalization.PrimitiveCellChains
import Formalization.CellTypeLocalZero
import Formalization.PrimitiveIdentityLift

set_option linter.style.header false

/-!
# Boundary decomposition by complete primitive cell type

An explicit primitive two-chain has finite support, hence only finitely many
complete oriented cell types occur in it.  This module isolates each such type,
reconstructs its part from the corresponding base-coefficient distribution,
and sums those parts to recover the full degree-two boundary.

The same finite decomposition remains valid after applying `d_*` to paths.
No claim that an individual summand lies in the identity subgroup is made here.
-/

noncomputable section

open scoped BigOperators

namespace GeneralSphereT.PathAlgebra

section OneType

variable {ι G : Type*} [AddCommGroup G]

local instance instDecidableEqPrimitiveCellTypeBoundaryDecomposition :
    DecidableEq (PrimitiveCellType ι G) := Classical.decEq _

/-- Insert a distribution of bases into the cells of one complete type. -/
def cellTypeInclusion (τ : PrimitiveCellType ι G) :
    Dist (Configuration ι G) →ₗ[ℤ] PrimitiveCellChain₂ ι G :=
  Finsupp.linearCombination ℤ fun c => primitiveCellGenerator τ c

@[simp]
theorem cellTypeInclusion_single
    (τ : PrimitiveCellType ι G) (c : Configuration ι G) (n : ℤ) :
    cellTypeInclusion τ (Finsupp.single c n) =
      Finsupp.single (τ, c) n := by
  simp [cellTypeInclusion, primitiveCellGenerator]

/-- Evaluation formula for insertion of one complete cell type. -/
theorem cellTypeInclusion_apply
    (τ : PrimitiveCellType ι G) (u : Dist (Configuration ι G))
    (σ : PrimitiveCellType ι G) (c : Configuration ι G) :
    cellTypeInclusion τ u (σ, c) =
      if σ = τ then u c else 0 := by
  classical
  induction u using Finsupp.induction with
  | zero => simp
  | single_add b n u _ _ ih =>
      simp only [map_add, cellTypeInclusion_single, Finsupp.add_apply, ih]
      by_cases hστ : σ = τ
      · subst σ
        simp [Finsupp.single_apply]
      · simp [hστ]

/--
Boundary contributed by a single complete cell type.  A point mass at `c` is
sent to the square or triangle boundary tagged by `τ` and based at `c`.
-/
def cellTypeBoundary (τ : PrimitiveCellType ι G) :
    Dist (Configuration ι G) →ₗ[ℤ]
      Path (Configuration ι G) (Configuration ι G) :=
  primitiveCellBoundary₂.comp (cellTypeInclusion τ)

@[simp]
theorem cellTypeBoundary_single
    (τ : PrimitiveCellType ι G) (c : Configuration ι G) (n : ℤ) :
    cellTypeBoundary τ (Finsupp.single c n) =
      n • primitiveCellBoundaryGenerator (τ, c) := by
  simp [cellTypeBoundary]

/-- The `τ`-part of a two-chain, reconstructed from its base coefficients. -/
def primitiveCellTypePart (τ : PrimitiveCellType ι G) :
    PrimitiveCellChain₂ ι G →ₗ[ℤ] PrimitiveCellChain₂ ι G :=
  (cellTypeInclusion τ).comp (primitiveCellTypeCoefficient τ)

/-- A type part retains exactly the cells with that complete tag. -/
theorem primitiveCellTypePart_apply
    (τ : PrimitiveCellType ι G) (Z : PrimitiveCellChain₂ ι G)
    (σ : PrimitiveCellType ι G) (c : Configuration ι G) :
    primitiveCellTypePart τ Z (σ, c) =
      if σ = τ then Z (σ, c) else 0 := by
  rw [primitiveCellTypePart, LinearMap.comp_apply,
    cellTypeInclusion_apply, primitiveCellTypeCoefficient_apply]
  by_cases hστ : σ = τ
  · subst σ
    rfl
  · simp [hστ]

/--
The boundary obtained from the collected `τ`-coefficient distribution is
literally the boundary of the `τ`-part of the original chain.
-/
theorem cellTypeBoundary_coefficient
    (τ : PrimitiveCellType ι G) (Z : PrimitiveCellChain₂ ι G) :
    cellTypeBoundary τ (primitiveCellTypeCoefficient τ Z) =
      primitiveCellBoundary₂ (primitiveCellTypePart τ Z) := by
  rfl

end OneType

section FiniteTypeSupport

variable {ι G : Type*} [AddCommGroup G]

/-- The finite set of complete cell types which actually occur in `Z`. -/
def primitiveCellTypeSupport (Z : PrimitiveCellChain₂ ι G) :
    Finset (PrimitiveCellType ι G) := by
  classical
  exact Z.support.image Prod.fst

/-- A nonzero cell coefficient puts its complete tag in the type support. -/
theorem mem_primitiveCellTypeSupport_of_ne
    (Z : PrimitiveCellChain₂ ι G)
    (τ : PrimitiveCellType ι G) (c : Configuration ι G)
    (hZ : Z (τ, c) ≠ 0) :
    τ ∈ primitiveCellTypeSupport Z := by
  classical
  rw [primitiveCellTypeSupport, Finset.mem_image]
  exact ⟨(τ, c), Finsupp.mem_support_iff.mpr hZ, rfl⟩

/-- Summing all finitely supported complete-type projections recovers `Z`. -/
theorem sum_primitiveCellTypePart (Z : PrimitiveCellChain₂ ι G) :
    ∑ τ ∈ primitiveCellTypeSupport Z, primitiveCellTypePart τ Z = Z := by
  classical
  ext cell
  rcases cell with ⟨σ, c⟩
  by_cases hσ : σ ∈ primitiveCellTypeSupport Z
  · simp [primitiveCellTypePart_apply, hσ]
  · have hzero : Z (σ, c) = 0 := by
      by_contra hne
      exact hσ (mem_primitiveCellTypeSupport_of_ne Z σ c hne)
    simp [primitiveCellTypePart_apply, hzero]

/--
Finite complete-type decomposition of the full primitive two-cell boundary.
-/
theorem primitiveCellBoundary₂_eq_sum_cellTypeBoundary
    (Z : PrimitiveCellChain₂ ι G) :
    primitiveCellBoundary₂ Z =
      ∑ τ ∈ primitiveCellTypeSupport Z,
        cellTypeBoundary τ (primitiveCellTypeCoefficient τ Z) := by
  calc
    primitiveCellBoundary₂ Z =
        primitiveCellBoundary₂
          (∑ τ ∈ primitiveCellTypeSupport Z,
            primitiveCellTypePart τ Z) := by
      rw [sum_primitiveCellTypePart]
    _ = ∑ τ ∈ primitiveCellTypeSupport Z,
          primitiveCellBoundary₂ (primitiveCellTypePart τ Z) := by
      simp only [map_sum]
    _ = ∑ τ ∈ primitiveCellTypeSupport Z,
          cellTypeBoundary τ (primitiveCellTypeCoefficient τ Z) := by
      apply Finset.sum_congr rfl
      intro τ hτ
      exact (cellTypeBoundary_coefficient τ Z).symm

end FiniteTypeSupport

section PhysicalPushforward

variable {ι G B : Type*} [AddCommGroup G] [AddCommGroup B]

/-- The contribution of one primitive cell type after applying `d_*`. -/
def mappedCellTypeBoundary
    (d : Configuration ι G →+ B) (τ : PrimitiveCellType ι G) :
    Dist (Configuration ι G) →ₗ[ℤ]
      Path (Configuration ι G) B :=
  (mapDPath d).comp (cellTypeBoundary τ)

@[simp]
theorem mappedCellTypeBoundary_single
    (d : Configuration ι G →+ B) (τ : PrimitiveCellType ι G)
    (c : Configuration ι G) (n : ℤ) :
    mappedCellTypeBoundary d τ (Finsupp.single c n) =
      n • mapDPath d (primitiveCellBoundaryGenerator (τ, c)) := by
  simp [mappedCellTypeBoundary]

/-- The complete-type boundary decomposition survives physical pushforward. -/
theorem mapDPath_primitiveCellBoundary₂_eq_sum_mappedCellTypeBoundary
    (d : Configuration ι G →+ B) (Z : PrimitiveCellChain₂ ι G) :
    mapDPath d (primitiveCellBoundary₂ Z) =
      ∑ τ ∈ primitiveCellTypeSupport Z,
        mappedCellTypeBoundary d τ
          (primitiveCellTypeCoefficient τ Z) := by
  rw [primitiveCellBoundary₂_eq_sum_cellTypeBoundary]
  simp [mappedCellTypeBoundary]

end PhysicalPushforward

end GeneralSphereT.PathAlgebra
