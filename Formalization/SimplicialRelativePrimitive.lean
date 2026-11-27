import Formalization.SimplicialFacetData
import Formalization.SimplicialCoboundarySquare
import Formalization.SimplicialConeContraction
import Formalization.CoordinateExtension

set_option linter.style.header false

/-!
# Relative primitive sections for finite simplicial cochains

This file carries out (2.22)--(2.24) for the actual ordered simplicial
coboundary.  A primitive is normalized on the closed star of its active
simplex by the explicit cone homotopy.  In positive degree the correction is
`d` of a zero-extended cochain; in degree zero it is a global constant.
-/

noncomputable section

namespace GeneralSphereT.SimplicialCochain

open GeneralSphereT.PathAlgebra

variable {V G : Type*} [LinearOrder V] [Fintype V] [AddCommGroup G]
variable (K : AbstractSimplicialComplex V)

omit [LinearOrder V] [Fintype V] in
/-- Every nondegenerate simplex has a vertex. -/
theorem simplex_nonempty {n : ℕ} (η : Simplex K n) : η.1.Nonempty := by
  apply Finset.card_pos.mp
  rw [η.2.2]
  omega

/-- A fixed apex vertex of a nondegenerate simplex. -/
def simplexApex {n : ℕ} (η : Simplex K n) : V :=
  η.1.min' (simplex_nonempty K η)

@[simp]
theorem simplexApex_mem {n : ℕ} (η : Simplex K n) :
    simplexApex K η ∈ η.1 :=
  Finset.min'_mem _ _

/-- Regard a nondegenerate simplex as an ungraded nonempty simplex. -/
def forgetDimension {n : ℕ} (η : Simplex K n) : NonemptySimplex K :=
  ⟨η.1, η.2.1⟩

@[simp]
theorem simplexApex_mem_forgetDimension {n : ℕ} (η : Simplex K n) :
    simplexApex K η ∈ (forgetDimension K η).1 :=
  simplexApex_mem K η

/-- The coordinate set of degree-`k` simplices in the closed star of `η`. -/
def closedStarSet {n : ℕ} (η : Simplex K n) (k : ℕ) :
    Set (Simplex K k) :=
  {τ | τ.1 ∪ η.1 ∈ K}

/-- Extend a closed-star cochain by zero to the whole complex. -/
def extendClosedStar {n : ℕ} (η : Simplex K n) (k : ℕ) :
    ClosedStarCochain K (forgetDimension K η) k G →+
      Cochain K k G :=
  coordinateExtension (closedStarSet K η k)

@[simp]
theorem restrictClosedStar_extendClosedStar {n k : ℕ}
    (η : Simplex K n)
    (c : ClosedStarCochain K (forgetDimension K η) k G) :
    restrictClosedStar K (forgetDimension K η) k
        (extendClosedStar K η k c) = c := by
  ext τ
  rw [restrictClosedStar_apply]
  change coordinateExtension (closedStarSet K η k) c τ.1 = c τ
  exact coordinateExtension_apply_mem (closedStarSet K η k) c τ.2

/-- A set-theoretically chosen global primitive of a physical coboundary. -/
def chosenPrimitive (n : ℕ) (a : CoboundaryGroup (G := G) K n) :
    Cochain K n G :=
  Classical.choose a.2

@[simp]
theorem coboundary_chosenPrimitive (n : ℕ)
    (a : CoboundaryGroup (G := G) K n) :
    coboundary K n (chosenPrimitive K n a) = a.1 :=
  Classical.choose_spec a.2

/-- Positive-degree normalized primitive attached to an active simplex. -/
def normalizedPrimitiveSucc (m : ℕ) (η : Simplex K (m + 1))
    (a : CoboundaryGroup (G := G) K (m + 1)) :
    Cochain K (m + 1) G :=
  let c := chosenPrimitive K (m + 1) a
  let b := coneHomotopy K (forgetDimension K η) (simplexApex K η)
    (simplexApex_mem_forgetDimension K η) m
      (restrictClosedStar K (forgetDimension K η) (m + 1) c)
  c - coboundary K m (extendClosedStar K η m b)

/-- The positive-degree normalization does not change the coboundary. -/
@[simp]
theorem coboundary_normalizedPrimitiveSucc (m : ℕ)
    (η : Simplex K (m + 1))
    (a : CoboundaryGroup (G := G) K (m + 1)) :
    coboundary K (m + 1) (normalizedPrimitiveSucc K m η a) = a.1 := by
  simp [normalizedPrimitiveSucc, map_sub]

/-- On the closed star, the normalized primitive is exactly `h(a)`. -/
theorem restrictClosedStar_normalizedPrimitiveSucc (m : ℕ)
    (η : Simplex K (m + 1))
    (a : CoboundaryGroup (G := G) K (m + 1)) :
    restrictClosedStar K (forgetDimension K η) (m + 1)
        (normalizedPrimitiveSucc K m η a) =
      coneHomotopy K (forgetDimension K η) (simplexApex K η)
        (simplexApex_mem_forgetDimension K η) (m + 1)
        (restrictClosedStar K (forgetDimension K η) (m + 2) a.1) := by
  let c := chosenPrimitive K (m + 1) a
  let h := coneHomotopy K (forgetDimension K η) (simplexApex K η)
    (simplexApex_mem_forgetDimension K η) m
      (restrictClosedStar K (forgetDimension K η) (m + 1) c)
  have hcontract := closedStar_contraction_positive
    (G := G) K (forgetDimension K η) (simplexApex K η)
      (simplexApex_mem_forgetDimension K η) m
        (restrictClosedStar K (forgetDimension K η) (m + 1) c)
  have hd :
      closedStarCoboundary K (forgetDimension K η) (m + 1)
          (restrictClosedStar K (forgetDimension K η) (m + 1) c) =
        restrictClosedStar K (forgetDimension K η) (m + 2) a.1 := by
    calc
      _ = restrictClosedStar K (forgetDimension K η) (m + 2)
          (coboundary K (m + 1) c) :=
        (LinearMap.congr_fun
          (restrictClosedStar_coboundary (G := G) K
            (forgetDimension K η) (m + 1)) c).symm
      _ = _ := by simp [c]
  change restrictClosedStar K (forgetDimension K η) (m + 1)
      (c - coboundary K m (extendClosedStar K η m h)) = _
  rw [map_sub]
  have hnat := LinearMap.congr_fun
    (restrictClosedStar_coboundary (G := G) K
      (forgetDimension K η) m)
    (extendClosedStar K η m h)
  simp only [LinearMap.comp_apply] at hnat
  rw [hnat, restrictClosedStar_extendClosedStar]
  nth_rewrite 1 [← hcontract]
  rw [hd]
  abel

end GeneralSphereT.SimplicialCochain
