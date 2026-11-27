import Formalization.OpenDisk.Locality
import Mathlib.Data.Finsupp.Fintype
import Mathlib.Topology.Instances.AddCircle.Real
import Mathlib.Topology.Homeomorph.Lemmas

set_option linter.style.header false

/-!
# The topology of local phase tables

The anchored-coordinate equivalence is a homeomorphism for the product
topology. Restriction to allowed supports gives a product of copies of the
coefficient group. For finite cochains and circle coefficients this is a
finite-dimensional torus, including the constant phase coordinate.
-/

noncomputable section

open scoped BigOperators
open GeneralSphereT.PathAlgebra

namespace OpenDisk

variable {ι G A Facet : Type*} [LinearOrder ι] [AddCommGroup G] [AddCommGroup A]
  [TopologicalSpace A] [IsTopologicalAddGroup A]

theorem continuous_anchoredCoordinate :
    Continuous (anchoredCoordinate (ι := ι) (G := G) (A := A)) := by
  apply continuous_pi
  intro c
  simp_rw [anchoredCoordinate_formula]
  fun_prop

theorem continuous_reconstructPhase :
    Continuous (reconstructPhase (ι := ι) (G := G) (A := A)) := by
  apply continuous_pi
  intro c
  unfold reconstructPhase
  fun_prop

/-- The full change to anchored phase coordinates respects the product topology. -/
def anchoredHomeomorph : (Configuration ι G → A) ≃ₜ (Configuration ι G → A) where
  toEquiv := anchoredEquiv
  continuous_toFun := continuous_anchoredCoordinate
  continuous_invFun := continuous_reconstructPhase

/-- Allowed interactions, together with all their nonzero input values. -/
abbrev AllowedConfiguration (facets : Facet → Set ι) :=
  {c : Configuration ι G // ∃ ρ, ∀ i ∈ c.support, i ∈ facets ρ}

/-- Local phase tables with the subspace topology from the full function space. -/
def LocalPhaseSpace (facets : Facet → Set ι) (A : Type*) [AddCommGroup A] :=
  {f : Configuration ι G → A // AnchoredLocal facets f}

instance (facets : Facet → Set ι) : TopologicalSpace (LocalPhaseSpace (G := G) facets A) :=
  inferInstanceAs (TopologicalSpace {f : Configuration ι G → A // AnchoredLocal facets f})

/-- Extend a table on allowed interactions by zero on all nonfaces. -/
def extendAllowed (facets : Facet → Set ι)
    (a : AllowedConfiguration (G := G) facets → A) (c : Configuration ι G) : A := by
  classical
  exact if h : ∃ ρ, ∀ i ∈ c.support, i ∈ facets ρ then a ⟨c, h⟩ else 0

theorem extendAllowed_local (facets : Facet → Set ι)
    (a : AllowedConfiguration (G := G) facets → A) :
    AnchoredLocal facets (reconstructPhase (extendAllowed facets a)) := by
  intro c hc
  rw [anchoredCoordinate_reconstruct]
  simp only [extendAllowed, dite_eq_right (not_exists.mpr hc)]

theorem continuous_extendAllowed (facets : Facet → Set ι) :
    Continuous (extendAllowed (G := G) (A := A) facets) := by
  classical
  apply continuous_pi
  intro c
  by_cases h : ∃ ρ, ∀ i ∈ c.support, i ∈ facets ρ
  · simpa only [extendAllowed, dite_eq_left h] using
      (continuous_apply (⟨c, h⟩ : AllowedConfiguration (G := G) facets) :
        Continuous (fun a : AllowedConfiguration (G := G) facets → A => a ⟨c, h⟩))
  · simp only [extendAllowed, dite_eq_right h]
    exact continuous_const

/-- The natural product-coordinate homeomorphism of the local phase space. -/
def localPhaseHomeomorph (facets : Facet → Set ι) :
    LocalPhaseSpace (G := G) facets A ≃ₜ (AllowedConfiguration (G := G) facets → A) where
  toFun f c := anchoredCoordinate f.val c.val
  invFun a := ⟨reconstructPhase (extendAllowed facets a), extendAllowed_local facets a⟩
  left_inv f := by
    apply Subtype.ext
    change reconstructPhase (extendAllowed facets (fun c => anchoredCoordinate f.val c.val)) = f.val
    have hext : extendAllowed facets (fun c => anchoredCoordinate f.val c.val) =
        anchoredCoordinate f.val := by
      funext c
      classical
      by_cases h : ∃ ρ, ∀ i ∈ c.support, i ∈ facets ρ
      · simp only [extendAllowed, dite_eq_left h]
      · simp only [extendAllowed, dite_eq_right h, f.property c (not_exists.mp h)]
    rw [hext, reconstruct_anchoredCoordinate]
  right_inv a := by
    funext c
    change anchoredCoordinate (reconstructPhase (extendAllowed facets a)) c.val = a c
    rw [anchoredCoordinate_reconstruct]
    simp only [extendAllowed, dite_eq_left c.property]
  continuous_toFun := by
    apply continuous_pi
    intro c
    exact (continuous_apply c.val).comp
      (continuous_anchoredCoordinate.comp continuous_subtype_val)
  continuous_invFun :=
    (continuous_reconstructPhase.comp (continuous_extendAllowed facets)).subtype_mk _

instance [Fintype ι] [Fintype G] (facets : Facet → Set ι) :
    Fintype (AllowedConfiguration (G := G) facets) := by
  classical
  unfold AllowedConfiguration
  infer_instance

/-- The number of independent circle coordinates in the local phase table. -/
def localPhaseDimension [Fintype ι] [Fintype G] (facets : Facet → Set ι) : ℕ :=
  Fintype.card (AllowedConfiguration (G := G) facets)

/-- The finite-dimensional torus conclusion in Theorem 1.2. -/
def localPhaseTorus [Fintype ι] [Fintype G] (facets : Facet → Set ι) :
    LocalPhaseSpace (G := G) facets (AddCircle (1 : ℝ)) ≃ₜ
      (Fin (localPhaseDimension (G := G) facets) → AddCircle (1 : ℝ)) :=
  (localPhaseHomeomorph facets).trans
    (Homeomorph.piCongrLeft (Y := fun _ => AddCircle (1 : ℝ))
      (Fintype.equivFin (AllowedConfiguration (G := G) facets)))

end OpenDisk
