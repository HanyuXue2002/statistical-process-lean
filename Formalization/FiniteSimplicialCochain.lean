import Formalization.RelativePrimitiveSection
import Mathlib.AlgebraicTopology.SimplicialComplex.Basic

set_option linter.style.header false

/-!
# Finite ordered simplicial cochains

This file realizes the abstract coordinate group used by the strict path model
as ordinary cochains on a finite ordered abstract simplicial complex.  A degree
`n` simplex is represented by its increasing finite vertex set, so its
orientation is fixed by the ambient vertex order.
-/

noncomputable section

open scoped BigOperators

namespace GeneralSphereT.SimplicialCochain

variable {V G : Type*} [LinearOrder V] [Fintype V] [AddCommGroup G]

/-- Oriented nondegenerate `n`-simplices, represented by increasing vertex
sets of cardinality `n+1`. -/
abbrev Simplex (K : AbstractSimplicialComplex V) (n : ℕ) :=
  {s : Finset V // s ∈ K ∧ s.card = n + 1}

/-- Integral-coordinate model for degree-`n` cochains. -/
abbrev Cochain (K : AbstractSimplicialComplex V) (n : ℕ) (G : Type*)
    [AddCommGroup G] :=
  GeneralSphereT.PathAlgebra.Configuration (Simplex K n) G

variable (K : AbstractSimplicialComplex V)

/-- Deleting one vertex of an `(n+1)`-simplex gives an `n`-simplex. -/
def eraseVertex {n : ℕ} (τ : Simplex K (n + 1))
    (v : V) (hv : v ∈ τ.1) : Simplex K n := by
  let s := τ.1.erase v
  have hcard : s.card = n + 1 := by
    simp [s, Finset.card_erase_of_mem hv, τ.2.2]
  have hsne : s.Nonempty := Finset.card_pos.mp (by omega)
  exact ⟨s, (K.isRelLowerSet_faces τ.2.1).2 (Finset.erase_subset _ _) hsne,
    hcard⟩

/-- Incidence sign of the face obtained by deleting `v`. -/
def incidenceSign {n : ℕ} (τ : Simplex K (n + 1)) (v : V) : ℤ :=
  (-1 : ℤ) ^ (τ.1.filter fun w => w < v).card

/-- The usual ordered simplicial coboundary, first as an additive map. -/
def coboundaryAddHom (n : ℕ) :
    Cochain K n G →+ Cochain K (n + 1) G where
  toFun c := Finsupp.equivFunOnFinite.symm fun τ =>
    ∑ v : τ.1, incidenceSign K τ v.1 • c (eraseVertex K τ v.1 v.2)
  map_zero' := by
    ext τ
    simp
  map_add' c c' := by
    ext τ
    simp [Finset.sum_add_distrib]

/-- The ordered simplicial coboundary as a `ℤ`-linear map. -/
def coboundary (n : ℕ) :
    Cochain K n G →ₗ[ℤ] Cochain K (n + 1) G :=
  (coboundaryAddHom K n).toIntLinearMap

@[simp]
theorem coboundary_apply (n : ℕ) (c : Cochain K n G)
    (τ : Simplex K (n + 1)) :
    coboundary K n c τ =
      ∑ v : τ.1,
        incidenceSign K τ v.1 • c (eraseVertex K τ v.1 v.2) :=
  rfl

/-- Degree-`n` faces contained in a fixed simplex. -/
def facesIn (n : ℕ) (σ : {s : Finset V // s ∈ K}) : Set (Simplex K n) :=
  {η | η.1 ⊆ σ.1}

/-- Restriction of cochains to the faces contained in `σ`. -/
def restrictCochain (n : ℕ) (σ : {s : Finset V // s ∈ K}) :
    Cochain K n G →+ GeneralSphereT.PathAlgebra.Configuration (facesIn K n σ) G :=
  GeneralSphereT.PathAlgebra.coordinateRestriction (facesIn K n σ)

omit [LinearOrder V] [Fintype V] in
@[simp]
theorem restrictCochain_apply (n : ℕ) (σ : {s : Finset V // s ∈ K})
    (c : Cochain K n G) (η : facesIn K n σ) :
    restrictCochain K n σ c η = c η.1 :=
  rfl

/-- A codimension-one face of a simplex contained in `σ` is still contained
in `σ`. -/
def eraseVertexIn {n : ℕ} (σ : {s : Finset V // s ∈ K})
    (τ : facesIn K (n + 1) σ) (v : V) (hv : v ∈ τ.1.1) :
    facesIn K n σ :=
  ⟨eraseVertex K τ.1 v hv,
    (Finset.erase_subset _ _).trans τ.2⟩

/-- Local coboundary on the simplex `σ`. -/
def localCoboundaryAddHom (n : ℕ) (σ : {s : Finset V // s ∈ K}) :
    GeneralSphereT.PathAlgebra.Configuration (facesIn K n σ) G →+
      GeneralSphereT.PathAlgebra.Configuration (facesIn K (n + 1) σ) G where
  toFun c := Finsupp.equivFunOnFinite.symm fun τ =>
    ∑ v : τ.1.1,
      incidenceSign K τ.1 v.1 • c (eraseVertexIn K σ τ v.1 v.2)
  map_zero' := by
    ext τ
    simp
  map_add' c c' := by
    ext τ
    simp [Finset.sum_add_distrib]

/-- Local coboundary as a `ℤ`-linear map. -/
def localCoboundary (n : ℕ) (σ : {s : Finset V // s ∈ K}) :
    GeneralSphereT.PathAlgebra.Configuration (facesIn K n σ) G →ₗ[ℤ]
      GeneralSphereT.PathAlgebra.Configuration (facesIn K (n + 1) σ) G :=
  (localCoboundaryAddHom K n σ).toIntLinearMap

@[simp]
theorem localCoboundary_apply (n : ℕ)
    (σ : {s : Finset V // s ∈ K})
    (c : GeneralSphereT.PathAlgebra.Configuration (facesIn K n σ) G)
    (τ : facesIn K (n + 1) σ) :
    localCoboundary K n σ c τ =
      ∑ v : τ.1.1,
        incidenceSign K τ.1 v.1 • c (eraseVertexIn K σ τ v.1 v.2) :=
  rfl

/-- Coboundary strictly commutes with restriction to a simplex. -/
theorem restrictCochain_coboundary (n : ℕ)
    (σ : {s : Finset V // s ∈ K}) :
    (restrictCochain (G := G) K (n + 1) σ).comp
        (coboundary K n).toAddMonoidHom =
      (localCoboundary K n σ).toAddMonoidHom.comp
        (restrictCochain (G := G) K n σ) := by
  ext c τ
  simp only [AddMonoidHom.comp_apply, restrictCochain_apply]
  apply Finset.sum_congr rfl
  intro v hv
  rfl

/-- The physical configuration group `B^{n+1}` is literally the range of the
coboundary. -/
abbrev CoboundaryGroup (n : ℕ) := LinearMap.range (coboundary (G := G) K n)

/-- Coboundary with codomain restricted to its range. -/
def coboundaryToRange (n : ℕ) :
    Cochain K n G →+ CoboundaryGroup (G := G) K n :=
  (coboundary K n).toAddMonoidHom.codRestrict
    (coboundary K n).range fun c => ⟨c, rfl⟩

theorem coboundaryToRange_surjective (n : ℕ) :
    Function.Surjective (coboundaryToRange (G := G) K n) := by
  rintro ⟨a, c, rfl⟩
  exact ⟨c, rfl⟩

/-- Restriction of a physical coboundary to a simplex, regarded simply as a
local cochain. -/
def restrictCoboundary (n : ℕ) (σ : {s : Finset V // s ∈ K}) :
    CoboundaryGroup (G := G) K n →+
      GeneralSphereT.PathAlgebra.Configuration (facesIn K (n + 1) σ) G :=
  (restrictCochain (G := G) K (n + 1) σ).comp
    (coboundary K n).range.subtype.toAddMonoidHom

end GeneralSphereT.SimplicialCochain
