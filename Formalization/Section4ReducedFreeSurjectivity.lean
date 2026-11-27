import Formalization.Section4ReducedFreeFiber
import Formalization.Section4DegreeZeroRow
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono

set_option linter.style.header false

/-!
# Section 4: surjectivity of the reduced-free standard-model map

For positive `q`, the disk-to-sphere map is degreewise epic as a chain map:
in its top degree it is an isomorphism, and away from that degree its target
is zero.  Dold--Kan transports this epimorphism to the standard simplicial map
`d : L(G,q) ⟶ K(G,q)`.  In a simplicial degree, epimorphisms of abelian
groups are surjective, so reduced freeness preserves the epimorphism by the
explicit reduced-distribution lifting theorem.

The totalized convention `L(G,0)=0` makes the assertion false in degree zero
unless `G=0`; all the positive-degree results therefore use `q+1` explicitly.
-/

noncomputable section

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits

namespace GeneralSphereT.StandardModels

open PathAlgebra

universe u

/-! ## The standard map is epic for positive `q` -/

/-- The defining disk-to-sphere chain map is an epimorphism. -/
theorem diskToSphereSucc_epi (G : AddCommGrpCat.{u}) (q : ℕ) :
    Epi (diskToSphereSucc G q) := by
  apply HomologicalComplex.epi_of_epi_f
  intro i
  by_cases hi : i = q + 1
  · subst i
    rw [diskToSphereSucc, HomologicalComplex.mkHomToSingle_f]
    infer_instance
  · exact
      (HomologicalComplex.isZero_single_obj_X
        (ComplexShape.down ℕ) (q + 1) G i hi).isInitial.epi_to _

/-- Dold--Kan transports the positive-degree disk projection to an
epimorphism of simplicial abelian groups. -/
theorem d_succ_epi (G : AddCommGrpCat.{u}) (q : ℕ) :
    Epi (d G (q + 1)) := by
  change Epi (denormalize.map (diskToSphereSucc G q))
  let _ : Epi (diskToSphereSucc G q) := diskToSphereSucc_epi G q
  have hepi : Epi
      ((CategoryTheory.Abelian.DoldKan.equivalence
        (A := AddCommGrpCat.{u})).inverse.map (diskToSphereSucc G q)) := by
    infer_instance
  simpa only [CategoryTheory.Abelian.DoldKan.equivalence_inverse] using hepi

/-- In every simplicial degree, `d : L(G,q+1) ⟶ K(G,q+1)` is surjective. -/
theorem d_succ_app_surjective (G : AddCommGrpCat.{u}) (q : ℕ)
    (Δ : SimplexCategoryᵒᵖ) :
    Function.Surjective ((d G (q + 1)).app Δ) := by
  let _ : Epi (d G (q + 1)) := d_succ_epi G q
  exact (AddCommGrpCat.epi_iff_surjective ((d G (q + 1)).app Δ)).mp
    inferInstance

/-! ## Reduced freeness preserves this epimorphism -/

/-- Reduced pushforward along `d` is surjective in every simplicial degree. -/
theorem reducedFreeMap_d_succ_app_surjective
    (G : AddCommGrpCat.{u}) (q : ℕ) (Δ : SimplexCategoryᵒᵖ) :
    Function.Surjective ((reducedFreeMap (d G (q + 1))).app Δ) := by
  change Function.Surjective (mapRedDist ((d G (q + 1)).app Δ).hom)
  exact PathAlgebra.mapRedDist_surjective_of_surjective
    ((d G (q + 1)).app Δ).hom (d_succ_app_surjective G q Δ)

/-- The induced reduced-free simplicial map is an epimorphism. -/
theorem reducedFreeMap_d_succ_epi (G : AddCommGrpCat.{u}) (q : ℕ) :
    Epi (reducedFreeMap (d G (q + 1))) := by
  apply (NatTrans.epi_iff_epi_app
    (reducedFreeMap (d G (q + 1)))).2
  intro Δ
  exact (AddCommGrpCat.epi_iff_surjective
    ((reducedFreeMap (d G (q + 1))).app Δ)).2
      (reducedFreeMap_d_succ_app_surjective G q Δ)

/-- The standard positive-degree fibre sequence is short exact:
`0 ⟶ F ⟶ reducedFree L ⟶ reducedFree K ⟶ 0`. -/
theorem FKernelSequence_shortExact_succ
    (G : AddCommGrpCat.{u}) (q : ℕ) :
    (FKernelSequence G (q + 1)).ShortExact := by
  let _ : Epi (reducedFreeMap (d G (q + 1))) :=
    reducedFreeMap_d_succ_epi G q
  exact ShortComplex.ShortExact.mk'
    (FKernelSequence_exact G (q + 1)) inferInstance inferInstance

/-! ## The totalized degree-zero convention -/

/-- At `q=0`, the chain-level map is epic exactly when `G` is the zero
object.  Thus the unconditional positive-degree theorem cannot be extended to
the totalized convention `L(G,0)=0`. -/
theorem diskToSphere_zero_epi_iff_isZero (G : AddCommGrpCat.{u}) :
    Epi (diskToSphere G 0) ↔ IsZero G := by
  constructor
  · intro hepi
    let _ : Epi (diskToSphere G 0) := hepi
    have hsphere : IsZero (sphereComplex G 0) := by
      apply IsZero.of_epi_eq_zero (diskToSphere G 0)
      rfl
    have hdegree : IsZero ((sphereComplex G 0).X 0) :=
      (HomologicalComplex.eval AddCommGrpCat (ComplexShape.down ℕ) 0).map_isZero
        hsphere
    exact hdegree.of_iso
      (HomologicalComplex.singleObjXSelf
        (ComplexShape.down ℕ) 0 G)
  · intro hG
    have hsphere : IsZero (sphereComplex G 0) :=
      (HomologicalComplex.single AddCommGrpCat
        (ComplexShape.down ℕ) 0).map_isZero hG
    exact hsphere.isInitial.epi_to (diskToSphere G 0)

/-- Equivalently, the totalized simplicial map `d : L(G,0) ⟶ K(G,0)` is
epic exactly in the degenerate case where `G` is zero. -/
theorem d_zero_epi_iff_isZero (G : AddCommGrpCat.{u}) :
    Epi (d G 0) ↔ IsZero G := by
  let e := CategoryTheory.Abelian.DoldKan.equivalence
    (A := AddCommGrpCat.{u})
  have hmap :
      Epi (e.inverse.map (diskToSphere G 0)) ↔
        Epi (diskToSphere G 0) :=
    e.inverse.epi_map_iff_epi (diskToSphere G 0)
  simpa only [e, CategoryTheory.Abelian.DoldKan.equivalence_inverse] using
    hmap.trans (diskToSphere_zero_epi_iff_isZero G)

/-- Pointwise form of the degree-zero exception: all simplicial-degree maps
are surjective exactly when `G` is zero. -/
theorem d_zero_all_app_surjective_iff_isZero (G : AddCommGrpCat.{u}) :
    (∀ Δ : SimplexCategoryᵒᵖ,
      Function.Surjective ((d G 0).app Δ)) ↔ IsZero G := by
  rw [← d_zero_epi_iff_isZero G]
  constructor
  · intro hsurj
    apply (NatTrans.epi_iff_epi_app (d G 0)).2
    intro Δ
    exact (AddCommGrpCat.epi_iff_surjective ((d G 0).app Δ)).2
      (hsurj Δ)
  · intro hepi
    let _ : Epi (d G 0) := hepi
    intro Δ
    exact (AddCommGrpCat.epi_iff_surjective ((d G 0).app Δ)).1
      inferInstance

end GeneralSphereT.StandardModels
