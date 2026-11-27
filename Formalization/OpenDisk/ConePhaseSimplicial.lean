import Formalization.OpenDisk.ConePhase
import Formalization.Section3ApexFreeCoboundary

/-!
# The concrete simplicial cone primitive

This module instantiates `ConePhase.Splitting` using the already verified
ordered simplicial cone contraction in this repository. Thus Lemma 3.7 is
proved on genuine finite ordered simplicial closed stars in every cochain
degree, including the degree-zero constant correction. No contraction identity
is an assumption of the theorems below.
-/

noncomputable section

set_option maxHeartbeats 2000000

namespace OpenDisk.ConePhaseSimplicial

open GeneralSphereT.SimplicialCochain

variable {V G P : Type*} [LinearOrder V] [Fintype V]
  [AddCommGroup G] [AddCommGroup P]

variable (K : AbstractSimplicialComplex V)

/-- The closed cochains for the actual ordered closed-star coboundary. -/
def closedCochains (η : {s : Finset V // s ∈ K}) (n : ℕ) :
    AddSubgroup (ClosedStarCochain K η n G) :=
  (closedStarCoboundaryAddHom (G := G) K η n).ker

/-- The splitting `cbase = hₚ d c`, constructed from the concrete incidence signs. -/
def coneSplitting (η : {s : Finset V // s ∈ K}) (p : V) (hp : p ∈ η.1) (n : ℕ) :
    ConePhase.Splitting (closedCochains (G := G) K η n) :=
  ConePhase.splittingOfDifferential (closedStarCoboundaryAddHom K η n)
    (coneHomotopyAddHom K η p hp n)
    (closedStarCoboundary_coneBottomReplacement K η p hp n)

@[simp] theorem coneSplitting_base (η : {s : Finset V // s ∈ K})
    (p : V) (hp : p ∈ η.1) (n : ℕ) (c : ClosedStarCochain K η n G) :
    (coneSplitting K η p hp n).base c =
      coneHomotopy K η p hp n (closedStarCoboundary K η n c) := rfl

/-- The primitive is the paper's explicit `R(cclosed, cbase)`. -/
def conePrimitive (η : {s : Finset V // s ∈ K}) (p : V) (hp : p ∈ η.1) (n : ℕ)
    (R : closedCochains (G := G) K η n → ClosedStarCochain K η n G → P) :
    ClosedStarCochain K η n G → P :=
  ConePhase.primitive (coneSplitting K η p hp n) R

/-- Lemma 3.7 for genuine ordered simplicial cochains, uniformly in all degrees. -/
theorem conePrimitive_difference (η : {s : Finset V // s ∈ K})
    (p : V) (hp : p ∈ η.1) (n : ℕ)
    {R : closedCochains (G := G) K η n → ClosedStarCochain K η n G → P}
    (hR : ConePhase.IsCocycle R) (z : closedCochains (G := G) K η n)
    (c : ClosedStarCochain K η n G) :
    conePrimitive K η p hp n R (c + z) - conePrimitive K η p hp n R c = R z c :=
  ConePhase.primitive_difference (coneSplitting K η p hp n) hR z c

/-- Apex-containing coordinates are zero on every base representative. -/
theorem coneSplitting_base_apex_zero (η : {s : Finset V // s ∈ K})
    (p : V) (hp : p ∈ η.1) (n : ℕ) (c : ClosedStarCochain K η n G)
    (σ : ClosedStarSimplex K η n) (hpσ : p ∈ σ.1.1) :
    (coneSplitting K η p hp n).base c σ = 0 :=
  coneBottomReplacement_apply_of_apex_mem K η p hp n c σ hpσ

/-- A cochain whose new cone coordinates vanish is exactly on the base slice. -/
theorem coneSplitting_base_eq_self (η : {s : Finset V // s ∈ K})
    (p : V) (hp : p ∈ η.1) (n : ℕ) (c : ClosedStarCochain K η n G)
    (hc : ∀ σ : ClosedStarSimplex K η n, p ∈ σ.1.1 → c σ = 0) :
    (coneSplitting K η p hp n).base c = c :=
  coneBottomReplacement_eq_self_of_apexFree K η p hp n c hc

/-- The canonical cap vanishes when its new cone coordinates are set to zero. -/
theorem conePrimitive_zero_slice (η : {s : Finset V // s ∈ K})
    (p : V) (hp : p ∈ η.1) (n : ℕ)
    {R : closedCochains (G := G) K η n → ClosedStarCochain K η n G → P}
    (hR : ConePhase.IsCocycle R) (c : ClosedStarCochain K η n G)
    (hc : ∀ σ : ClosedStarSimplex K η n, p ∈ σ.1.1 → c σ = 0) :
    conePrimitive K η p hp n R c = 0 := by
  conv_lhs => rw [← coneSplitting_base_eq_self K η p hp n c hc]
  exact ConePhase.primitive_base (coneSplitting K η p hp n) hR c

/-- In cochain degree zero the closed part is precisely the constant value at
the cone apex, so the `q = 1` case has no missing augmentation term. -/
theorem coneSplitting_closedPart_zero (η : {s : Finset V // s ∈ K})
    (p : V) (hp : p ∈ η.1) (c : ClosedStarCochain K η 0 G) :
    ((coneSplitting K η p hp 0).closedPart c : ClosedStarCochain K η 0 G) =
      closedStarConstant K η (closedStarAugmentation K η p hp c) := by
  rw [ConePhase.Splitting.coe_closedPart, coneSplitting_base,
    closedStar_contraction_zero]
  abel

end OpenDisk.ConePhaseSimplicial
