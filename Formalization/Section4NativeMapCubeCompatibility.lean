import Formalization.Section4NativeMapLocalDistributions

set_option linter.style.header false
set_option backward.isDefEq.respectTransparency false

/-!
# Cube-coordinate compatibility of the local distributions of a native map

The local distributions obtained by evaluating a simplicial map agree under
restriction.  A Boolean cube supported in two simplices is supported in their
nonempty intersection, so its coefficient can be read after restricting to
that common face.  This is precisely the compatibility needed by the integral
cube gluing construction.
-/

noncomputable section

open CategoryTheory Opposite Simplicial

namespace GeneralSphereT.SimplicialCochain

open GeneralSphereT.PathAlgebra
open GeneralSphereT.StandardModels
open GeneralSphereT.Section4

universe u

variable {V G : Type u} [LinearOrder V] [Fintype V] [AddCommGroup G]
variable (M : AbstractSimplicialComplex V) (q : ℕ)

local instance nativeCubeSimplexColexOrder : LinearOrder (Simplex M q) :=
  LinearOrder.lift'
    (fun η : Simplex M q => toColex η.1)
    ((toColex : Finset V ≃ Colex (Finset V)).injective.comp
      Subtype.val_injective)

/-- A cube coefficient supported in `θ` is unchanged when a local
distribution on `ρ` is restricted to `θ`.  The proof compares both local
coefficients with the same coefficient after extension to the global cochain
group. -/
theorem reducedCubeCoefficient_eq_of_facetRestriction
    (θ ρ : NonemptySimplex M)
    (uθ : RedDist (Configuration (facesIn M q θ) G))
    (uρ : RedDist (Configuration (facesIn M q ρ) G))
    (hu : mapRedDist (facetConfigurationRestriction M q θ ρ) uρ = uθ)
    (c : NonzeroConfiguration (Simplex M q) G)
    (hθ : ∀ i ∈ c.1.support, i ∈ facesIn M q θ)
    (hρ : ∀ i ∈ c.1.support, i ∈ facesIn M q ρ) :
    (reducedCubeBasis (G := G)).repr uθ
        (restrictNonzeroConfiguration (facesIn M q θ) c hθ) =
      (reducedCubeBasis (G := G)).repr uρ
        (restrictNonzeroConfiguration (facesIn M q ρ) c hρ) := by
  let U : RedDist (Cochain M q G) :=
    mapRedDist (coordinateExtension (facesIn M q ρ)) uρ
  have hUρ :
      mapRedDist (coordinateRestriction (facesIn M q ρ)) U = uρ := by
    change mapRedDist (coordinateRestriction (facesIn M q ρ))
        (mapRedDist (coordinateExtension (facesIn M q ρ)) uρ) = uρ
    rw [GeneralSphereT.StandardModels.mapRedDist_comp_apply]
    have hcomp :
        (coordinateRestriction (facesIn M q ρ)).comp
            (coordinateExtension (facesIn M q ρ)) =
          AddMonoidHom.id (Configuration (facesIn M q ρ) G) := by
      apply AddMonoidHom.ext
      intro a
      exact coordinateRestriction_coordinateExtension
        (facesIn M q ρ) a
    rw [hcomp]
    exact LinearMap.congr_fun
      (GeneralSphereT.StandardModels.mapRedDist_id
        (X := Configuration (facesIn M q ρ) G)) uρ
  have hUθ :
      mapRedDist (coordinateRestriction (facesIn M q θ)) U = uθ := by
    change mapRedDist (coordinateRestriction (facesIn M q θ))
        (mapRedDist (coordinateExtension (facesIn M q ρ)) uρ) = uθ
    rw [GeneralSphereT.StandardModels.mapRedDist_comp_apply]
    change mapRedDist (facetConfigurationRestriction M q θ ρ) uρ = uθ
    exact hu
  rw [reducedCube_repr_eq_cubeCoefficient,
    reducedCube_repr_eq_cubeCoefficient]
  have hcoeffθ := LinearMap.congr_fun
    (cubeCoefficient_mapDist_coordinateRestriction (G := G)
      (facesIn M q θ) c.1 hθ) U.1
  have hcoeffρ := LinearMap.congr_fun
    (cubeCoefficient_mapDist_coordinateRestriction (G := G)
      (facesIn M q ρ) c.1 hρ) U.1
  simp only [LinearMap.comp_apply] at hcoeffθ hcoeffρ
  have hdistθ :
      mapDist (coordinateRestriction (facesIn M q θ)) U.1 = uθ.1 :=
    congrArg Subtype.val hUθ
  have hdistρ :
      mapDist (coordinateRestriction (facesIn M q ρ)) U.1 = uρ.1 :=
    congrArg Subtype.val hUρ
  rw [hdistθ] at hcoeffθ
  rw [hdistρ] at hcoeffρ
  exact hcoeffθ.trans hcoeffρ.symm

/-- The local reduced distributions extracted from a native simplicial map
have a single coefficient for every global Boolean cube visible in more than
one simplex. -/
theorem nativeMapLocalDistribution_cubeCoefficientCompatible
    (f : orderedComplexSSet M ⟶
      underlyingSSet (reducedFree (L (AddCommGrpCat.of G) (q + 1)))) :
    CubeCoefficientCompatible
      (fun σ : NonemptySimplex M => facesIn M q σ)
      (nativeMapLocalDistribution M q f) := by
  intro c ρ σ hρ hσ
  have hsupp : c.1.support.Nonempty :=
    Finsupp.support_nonempty_iff.mpr c.2
  obtain ⟨η, hη⟩ := hsupp
  have hηρ : η.1 ⊆ ρ.1 := hρ η hη
  have hησ : η.1 ⊆ σ.1 := hσ η hη
  have hinterNonempty : (ρ.1 ∩ σ.1).Nonempty := by
    obtain ⟨v, hv⟩ := (M.isRelLowerSet_faces η.2.1).1
    exact ⟨v, Finset.mem_inter.mpr ⟨hηρ hv, hησ hv⟩⟩
  have hinterM : ρ.1 ∩ σ.1 ∈ M :=
    (M.isRelLowerSet_faces ρ.2).2 Finset.inter_subset_left hinterNonempty
  let θ : NonemptySimplex M := ⟨ρ.1 ∩ σ.1, hinterM⟩
  have hθρ : θ.1 ⊆ ρ.1 := Finset.inter_subset_left
  have hθσ : θ.1 ⊆ σ.1 := Finset.inter_subset_right
  have hθ : ∀ i ∈ c.1.support, i ∈ facesIn M q θ := by
    intro i hi
    exact Finset.subset_inter (hρ i hi) (hσ i hi)
  have hθρcoeff := reducedCubeCoefficient_eq_of_facetRestriction
    (G := G) M q θ ρ
      (nativeMapLocalDistribution M q f θ)
      (nativeMapLocalDistribution M q f ρ)
      (nativeMapLocalDistribution_restriction (G := G)
        M q f θ ρ hθρ)
      c hθ hρ
  have hθσcoeff := reducedCubeCoefficient_eq_of_facetRestriction
    (G := G) M q θ σ
      (nativeMapLocalDistribution M q f θ)
      (nativeMapLocalDistribution M q f σ)
      (nativeMapLocalDistribution_restriction (G := G)
        M q f θ σ hθσ)
      c hθ hσ
  exact hθρcoeff.symm.trans hθσcoeff

end GeneralSphereT.SimplicialCochain
