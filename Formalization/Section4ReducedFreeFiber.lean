import Formalization.Section4DoldKanModels
import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Kernels
import Mathlib.CategoryTheory.Abelian.Exact

set_option linter.style.header false

/-!
# Section 4: reduced free simplicial groups and the fibre `F(G,q)`

This file applies the paper's reduced-distribution construction degreewise to
a simplicial abelian group.  In degree `n`, `reducedFree A` is literally
`RedDist (A.obj Δ)`, the kernel of the coefficient-sum augmentation on the
free integral distribution group.  Thus no new model of the reduced free
abelian group is introduced here.

The construction is functorial, so the standard coboundary
`d : L(G,q) ⟶ K(G,q)` induces a simplicial map on reduced distributions.  We
define `F(G,q)` to be its categorical kernel.  The final comparison with the
concrete kernel records the corresponding degreewise membership formula.
-/

noncomputable section

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits

namespace GeneralSphereT.StandardModels

open PathAlgebra

universe u

section ReducedFree

variable {X Y Z : Type u}
variable [AddCommGroup X] [AddCommGroup Y] [AddCommGroup Z]

@[simp]
theorem mapRedDist_id :
    mapRedDist (AddMonoidHom.id X) =
      LinearMap.id (R := ℤ) (M := RedDist X) := by
  apply LinearMap.ext
  intro z
  apply Subtype.ext
  change Finsupp.lmapDomain ℤ ℤ id z.1 = z.1
  exact DFunLike.congr_fun (Finsupp.lmapDomain_id ℤ ℤ) z.1

theorem mapRedDist_comp (f : X →+ Y) (g : Y →+ Z) :
    mapRedDist (g.comp f) =
      (mapRedDist g).comp (mapRedDist f) := by
  apply LinearMap.ext
  intro z
  apply Subtype.ext
  change Finsupp.lmapDomain ℤ ℤ (g ∘ f) z.1 =
    Finsupp.lmapDomain ℤ ℤ g (Finsupp.lmapDomain ℤ ℤ f z.1)
  exact DFunLike.congr_fun (Finsupp.lmapDomain_comp ℤ ℤ f g) z.1

@[simp]
theorem mapRedDist_comp_apply (f : X →+ Y) (g : Y →+ Z)
    (z : RedDist X) :
    mapRedDist g (mapRedDist f z) = mapRedDist (g.comp f) z := by
  exact (LinearMap.congr_fun (mapRedDist_comp f g) z).symm

end ReducedFree

/-- Apply the augmentation-zero free-distribution construction in every
simplicial degree. -/
def reducedFree (A : SimplicialObject AddCommGrpCat.{u}) :
    SimplicialObject AddCommGrpCat.{u} where
  obj Δ := AddCommGrpCat.of (RedDist (A.obj Δ))
  map θ := AddCommGrpCat.ofHom (mapRedDist (A.map θ).hom).toAddMonoidHom
  map_id Δ := by
    rw [A.map_id]
    apply AddCommGrpCat.ext
    intro z
    exact LinearMap.congr_fun mapRedDist_id z
  map_comp θ φ := by
    rw [A.map_comp]
    apply AddCommGrpCat.ext
    intro z
    change mapRedDist ((A.map φ).hom.comp (A.map θ).hom) z =
      mapRedDist (A.map φ).hom (mapRedDist (A.map θ).hom z)
    exact (mapRedDist_comp_apply (A.map θ).hom (A.map φ).hom z).symm

@[simp]
theorem reducedFree_map_apply
    (A : SimplicialObject AddCommGrpCat.{u}) {Δ Δ' : SimplexCategoryᵒᵖ}
    (θ : Δ ⟶ Δ') (z : RedDist (A.obj Δ)) :
    (reducedFree A).map θ z = mapRedDist (A.map θ).hom z :=
  rfl

/-- A simplicial homomorphism induces a simplicial homomorphism on reduced
free integral distributions. -/
def reducedFreeMap {A B : SimplicialObject AddCommGrpCat.{u}} (f : A ⟶ B) :
    reducedFree A ⟶ reducedFree B where
  app Δ := AddCommGrpCat.ofHom (mapRedDist (f.app Δ).hom).toAddMonoidHom
  naturality Δ Δ' θ := by
    apply AddCommGrpCat.ext
    intro z
    change RedDist (A.obj Δ) at z
    change mapRedDist (f.app Δ').hom (mapRedDist (A.map θ).hom z) =
      mapRedDist (B.map θ).hom (mapRedDist (f.app Δ).hom z)
    have h : (f.app Δ').hom.comp (A.map θ).hom =
        (B.map θ).hom.comp (f.app Δ).hom :=
      congrArg (fun k => k.hom) (f.naturality θ)
    calc
      _ = mapRedDist ((f.app Δ').hom.comp (A.map θ).hom) z :=
        mapRedDist_comp_apply (A.map θ).hom (f.app Δ').hom z
      _ = mapRedDist ((B.map θ).hom.comp (f.app Δ).hom) z := by rw [h]
      _ = _ :=
        (mapRedDist_comp_apply (f.app Δ).hom (B.map θ).hom z).symm

@[simp]
theorem reducedFreeMap_app_apply
    {A B : SimplicialObject AddCommGrpCat.{u}} (f : A ⟶ B)
    (Δ : SimplexCategoryᵒᵖ) (z : RedDist (A.obj Δ)) :
    (reducedFreeMap f).app Δ z = mapRedDist (f.app Δ).hom z :=
  rfl

/-- The reduced-free construction as an endofunctor on simplicial abelian
groups. -/
def reducedFreeFunctor :
    SimplicialObject AddCommGrpCat.{u} ⥤
      SimplicialObject AddCommGrpCat.{u} where
  obj := reducedFree
  map := reducedFreeMap
  map_id A := by
    ext Δ z
    exact LinearMap.congr_fun mapRedDist_id z
  map_comp f g := by
    ext Δ z
    change mapRedDist ((g.app Δ).hom.comp (f.app Δ).hom) z =
      mapRedDist (g.app Δ).hom (mapRedDist (f.app Δ).hom z)
    exact (mapRedDist_comp_apply (f.app Δ).hom (g.app Δ).hom z).symm

section Fibre

variable (G : AddCommGrpCat.{u}) (q : ℕ)

/-- The simplicial fibre in Section 4: the kernel of reduced-distribution
pushforward along `d : L(G,q) ⟶ K(G,q)`. -/
abbrev F : SimplicialObject AddCommGrpCat.{u} :=
  kernel (reducedFreeMap (d G q))

/-- The kernel inclusion `F(G,q) ⟶ reducedFree (L(G,q))`. -/
abbrev Fι : F G q ⟶ reducedFree (L G q) :=
  kernel.ι (reducedFreeMap (d G q))

/-- The defining kernel equation. -/
theorem F_condition :
    Fι G q ≫ reducedFreeMap (d G q) = 0 :=
  kernel.condition (reducedFreeMap (d G q))

/-- The first two arrows of the standard sequence are exact by construction:
`F(G,q)` is the categorical kernel of reduced pushforward along `d`. -/
abbrev FKernelSequence : ShortComplex
    (SimplicialObject AddCommGrpCat.{u}) :=
  ShortComplex.mk (Fι G q) (reducedFreeMap (d G q)) (F_condition G q)

/-- Exactness at `reducedFree (L(G,q))` in the standard fibre sequence. -/
theorem FKernelSequence_exact : (FKernelSequence G q).Exact :=
  ShortComplex.exact_kernel (reducedFreeMap (d G q))

/-- In each simplicial degree, the abstract functor-category kernel is
canonically the ordinary kernel subgroup. -/
def FDegreeIso (Δ : SimplexCategoryᵒᵖ) :
    (F G q).obj Δ ≅
      AddCommGrpCat.of ((reducedFreeMap (d G q)).app Δ).hom.ker :=
  PreservesKernel.iso
      ((evaluation SimplexCategoryᵒᵖ AddCommGrpCat.{u}).obj Δ)
      (reducedFreeMap (d G q)) ≪≫
    AddCommGrpCat.kernelIsoKer ((reducedFreeMap (d G q)).app Δ)

/-- Under `FDegreeIso`, the simplicial kernel inclusion is the ordinary
subgroup inclusion. -/
theorem FDegreeIso_hom_comp_subtype (Δ : SimplexCategoryᵒᵖ) :
    (FDegreeIso G q Δ).hom ≫
        AddCommGrpCat.ofHom
          (AddSubgroup.subtype
            ((reducedFreeMap (d G q)).app Δ).hom.ker) =
      (Fι G q).app Δ := by
  simp only [FDegreeIso, Iso.trans_hom, Category.assoc,
    AddCommGrpCat.kernelIsoKer_hom_comp_subtype,
    PreservesKernel.iso_hom]
  simpa using
    (kernelComparison_comp_ι (f := reducedFreeMap (d G q))
      ((evaluation SimplexCategoryᵒᵖ AddCommGrpCat.{u}).obj Δ))

/-- Degreewise membership formula: every element of `F(G,q)` is represented
by an augmentation-zero distribution on `L(G,q)` whose pushforward along
`d` is zero. -/
@[simp]
theorem F_degree_mem (Δ : SimplexCategoryᵒᵖ) (x : (F G q).obj Δ) :
    (reducedFreeMap (d G q)).app Δ ((FDegreeIso G q Δ).hom x).1 = 0 :=
  ((FDegreeIso G q Δ).hom x).2

/-- Conversely, a degreewise reduced distribution killed by `d_*` gives an
element of `F(G,q)`. -/
def FDegreeMk (Δ : SimplexCategoryᵒᵖ)
    (z : (reducedFree (L G q)).obj Δ)
    (hz : (reducedFreeMap (d G q)).app Δ z = 0) :
    (F G q).obj Δ :=
  (FDegreeIso G q Δ).inv ⟨z, hz⟩

@[simp]
theorem FDegreeMk_inclusion (Δ : SimplexCategoryᵒᵖ)
    (z : (reducedFree (L G q)).obj Δ)
    (hz : (reducedFreeMap (d G q)).app Δ z = 0) :
    (Fι G q).app Δ (FDegreeMk G q Δ z hz) = z := by
  have h := ConcreteCategory.congr_hom
    (FDegreeIso_hom_comp_subtype G q Δ) (FDegreeMk G q Δ z hz)
  simpa [FDegreeMk] using h.symm

/-- The kernel condition written directly in the paper's notation: a reduced
distribution belongs to the degree-`Δ` fibre exactly when its reduced
pushforward is zero. -/
theorem F_degree_membership_iff (Δ : SimplexCategoryᵒᵖ)
    (z : (reducedFree (L G q)).obj Δ) :
    (∃ x : (F G q).obj Δ, (Fι G q).app Δ x = z) ↔
      (reducedFreeMap (d G q)).app Δ z = 0 := by
  constructor
  · rintro ⟨x, rfl⟩
    have h := ConcreteCategory.congr_hom
      (NatTrans.congr_app (F_condition G q) Δ) x
    change (reducedFreeMap (d G q)).app Δ ((Fι G q).app Δ x) = 0 at h
    exact h
  · intro hz
    exact ⟨FDegreeMk G q Δ z hz, FDegreeMk_inclusion G q Δ z hz⟩

end Fibre

end GeneralSphereT.StandardModels
