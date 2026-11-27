import Formalization.PathAlgebra

set_option linter.style.header false

/-!
# Primitive and configuration cells

This module formalizes the elementary path algebra behind equations (2.27),
(2.29), and (2.32).  A single displacement map covers both the primitive and
configuration versions.  Locality and support enter only later.
-/

noncomputable section

namespace GeneralSphereT.PathAlgebra

variable {I X : Type*} [AddCommGroup I] [AddCommGroup X]

/-- Translate the base point of every raw edge by `u`. -/
def rawBaseTranslation (u : X) : RawPath I X →ₗ[ℤ] Path I X :=
  Finsupp.linearCombination ℤ fun p => edge p.1 (p.2 + u)

@[simp]
theorem rawBaseTranslation_rawEdge (u : X) (r : I) (x : X) :
    rawBaseTranslation u (rawEdge r x) = edge r (x + u) := by
  simp [rawBaseTranslation, rawEdge]

/-- Base translation kills every zero-increment relation. -/
theorem zeroIncrement_le_rawBaseTranslation_ker (u : X) :
    zeroIncrement I X ≤ LinearMap.ker (rawBaseTranslation u) := by
  change Submodule.span ℤ
      (Set.range fun x : X => Finsupp.single ((0 : I), x) 1) ≤
    LinearMap.ker (rawBaseTranslation u)
  rw [Submodule.span_le]
  rintro _ ⟨x, rfl⟩
  change rawBaseTranslation u (rawEdge 0 x) = 0
  simp

/-- The induced base translation `T_u` on the path quotient. -/
def baseTranslation (u : X) : Path I X →ₗ[ℤ] Path I X :=
  (zeroIncrement I X).liftQ
    (rawBaseTranslation u) (zeroIncrement_le_rawBaseTranslation_ker u)

@[simp]
theorem baseTranslation_edge (u : X) (r : I) (x : X) :
    baseTranslation u (edge r x) = edge r (x + u) := by
  simp [baseTranslation, edge]

/-- The cross-square from (2.3), with displacement map `φ`. -/
def square (φ : I →+ X) (s t : I) (x : X) : Path I X :=
  edge s x + edge t (x + φ s) - edge s (x + φ t) - edge t x

/-- The three-edge triangle from (2.29), with displacement map `φ`. -/
def triangle (φ : I →+ X) (g h : I) (x : X) : Path I X :=
  edge g x + edge h (x + φ g) - edge (g + h) x

/-- Every cross-square is a boundary-zero path. -/
@[simp]
theorem boundary_square (φ : I →+ X) (s t : I) (x : X) :
    boundary φ (square φ s t x) = 0 := by
  simp only [square, map_sub, map_add, boundary_edge]
  abel_nf

/-- Every triangle is a boundary-zero path. -/
@[simp]
theorem boundary_triangle (φ : I →+ X) (g h : I) (x : X) :
    boundary φ (triangle φ g h x) = 0 := by
  simp only [triangle, map_sub, map_add, boundary_edge, map_add]
  abel_nf

/-- A square with zero first increment vanishes in the path quotient. -/
@[simp]
theorem square_zero_left (φ : I →+ X) (t : I) (x : X) :
    square φ 0 t x = 0 := by
  simp [square]

/-- A square with zero second increment vanishes in the path quotient. -/
@[simp]
theorem square_zero_right (φ : I →+ X) (s : I) (x : X) :
    square φ s 0 x = 0 := by
  simp [square]

/-- A triangle with zero first increment vanishes in the path quotient. -/
@[simp]
theorem triangle_zero_left (φ : I →+ X) (h : I) (x : X) :
    triangle φ 0 h x = 0 := by
  simp [triangle]

/-- A triangle with zero second increment vanishes in the path quotient. -/
@[simp]
theorem triangle_zero_right (φ : I →+ X) (g : I) (x : X) :
    triangle φ g 0 x = 0 := by
  simp [triangle]

/--
Equation (2.32): translating a triangle across a transverse increment is the
alternating sum of three cross-squares.
-/
theorem translate_triangle_sub_triangle (φ : I →+ X) (g h t : I) (x : X) :
    baseTranslation (φ t) (triangle φ g h x) - triangle φ g h x =
      square φ (g + h) t x - square φ g t x -
        baseTranslation (φ g) (square φ h t x) := by
  simp only [triangle, square, map_sub, map_add, baseTranslation_edge, map_add]
  abel_nf

end GeneralSphereT.PathAlgebra
