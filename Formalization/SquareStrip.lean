import Formalization.Cells

set_option linter.style.header false

/-!
# Finite words and the square-strip identity

This module isolates the path algebra in (3.14)--(3.16).  A list records the
order in which a word is traversed.  The main result proves the square-strip
identity for an arbitrary finite word; the cone-specific support argument is
separate.
-/

noncomputable section

namespace GeneralSphereT.PathAlgebra

variable {I X : Type*} [AddCommGroup I] [AddCommGroup X]

/-- The total increment of a finite ordered word. -/
def wordIncrement : List I → I
  | [] => 0
  | u :: word => u + wordIncrement word

/-- The endpoint reached by a word with displacement map `φ`. -/
def wordEndpoint (φ : I →+ X) (word : List I) (x : X) : X :=
  x + φ (wordIncrement word)

/-- The path obtained by traversing a finite word from the base `x`. -/
def wordPath (φ : I →+ X) : List I → X → Path I X
  | [], _ => 0
  | u :: word, x => edge u x + wordPath φ word (x + φ u)

/-- The difference between the one-edge path labelled `t` and a word path. -/
def ell (φ : I →+ X) (t : I) (word : List I) (x : X) : Path I X :=
  edge t x - wordPath φ word x

/-- The successive squares swept out by translating a word by `r`. -/
def squareStrip (φ : I →+ X) : List I → I → X → Path I X
  | [], _, _ => 0
  | u :: word, r, x =>
      square φ u r x + squareStrip φ word r (x + φ u)

/-- The base-translation difference `Δ_r = T_{φ r} - 1` on paths. -/
def pathDifference (φ : I →+ X) (r : I) (p : Path I X) : Path I X :=
  baseTranslation (φ r) p - p

@[simp]
theorem pathDifference_add (φ : I →+ X) (r : I) (p q : Path I X) :
    pathDifference φ r (p + q) = pathDifference φ r p + pathDifference φ r q := by
  simp only [pathDifference, map_add]
  abel_nf

@[simp]
theorem pathDifference_sub (φ : I →+ X) (r : I) (p q : Path I X) :
    pathDifference φ r (p - q) = pathDifference φ r p - pathDifference φ r q := by
  simp only [pathDifference, map_sub]
  abel_nf

/-- Moving one edge across `r` differs from the endpoint correction by a square. -/
theorem pathDifference_edge (φ : I →+ X) (u r : I) (x : X) :
    pathDifference φ r (edge u x) =
      edge r (x + φ u) - edge r x - square φ u r x := by
  simp only [pathDifference, baseTranslation_edge, square]
  abel_nf

/-- A word path has the expected telescoping boundary. -/
@[simp]
theorem boundary_wordPath (φ : I →+ X) (word : List I) (x : X) :
    boundary φ (wordPath φ word x) =
      bracket (wordEndpoint φ word x) - bracket x := by
  induction word generalizing x with
  | nil =>
      simp [wordPath, wordEndpoint, wordIncrement]
  | cons u word ih =>
      simp only [wordPath, wordEndpoint, wordIncrement, map_add, boundary_edge, ih]
      abel_nf

/-- The boundary of `ell` is exactly its endpoint discrepancy. -/
theorem boundary_ell (φ : I →+ X) (t : I) (word : List I) (x : X) :
    boundary φ (ell φ t word x) =
      bracket (x + φ t) - bracket (wordEndpoint φ word x) := by
  simp only [ell, map_sub, boundary_edge, boundary_wordPath]
  abel_nf

/-- The endpoint hypothesis in (3.16) makes `ell` a closed path. -/
@[simp]
theorem boundary_ell_of_endpoint
    (φ : I →+ X) (t : I) (word : List I) (x : X)
    (h : φ (wordIncrement word) = φ t) :
    boundary φ (ell φ t word x) = 0 := by
  rw [boundary_ell]
  simp [wordEndpoint, h]

/--
Translating a finite word gives its square strip and the edge joining the old
and new word endpoints.
-/
theorem pathDifference_wordPath
    (φ : I →+ X) (word : List I) (r : I) (x : X) :
    pathDifference φ r (wordPath φ word x) =
      edge r (wordEndpoint φ word x) - edge r x - squareStrip φ word r x := by
  induction word generalizing x with
  | nil =>
      simp [pathDifference, wordPath, wordEndpoint, wordIncrement, squareStrip]
  | cons u word ih =>
      rw [wordPath, pathDifference_add, pathDifference_edge, ih]
      simp only [wordEndpoint, wordIncrement, map_add, squareStrip]
      abel_nf

/-- The square-strip formula before equating the two endpoints. -/
theorem pathDifference_ell
    (φ : I →+ X) (t : I) (word : List I) (r : I) (x : X) :
    pathDifference φ r (ell φ t word x) =
      squareStrip φ word r x - square φ t r x +
        edge r (x + φ t) - edge r (wordEndpoint φ word x) := by
  rw [ell, pathDifference_sub, pathDifference_edge, pathDifference_wordPath]
  abel_nf

/-- Equation (3.16), for an arbitrary finite word. -/
theorem squareStrip_identity
    (φ : I →+ X) (t : I) (word : List I) (r : I) (x : X)
    (h : φ (wordIncrement word) = φ t) :
    baseTranslation (φ r) (ell φ t word x) - ell φ t word x =
      squareStrip φ word r x - square φ t r x := by
  change pathDifference φ r (ell φ t word x) = _
  rw [pathDifference_ell]
  simp [wordEndpoint, h]

/-- Every square strip has zero boundary. -/
@[simp]
theorem boundary_squareStrip
    (φ : I →+ X) (word : List I) (r : I) (x : X) :
    boundary φ (squareStrip φ word r x) = 0 := by
  induction word generalizing x with
  | nil => simp [squareStrip]
  | cons u word ih => simp [squareStrip, ih]

end GeneralSphereT.PathAlgebra
