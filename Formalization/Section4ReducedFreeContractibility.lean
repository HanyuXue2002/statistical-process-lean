import Formalization.Section4DoldKanHomology
import Formalization.Section4ReducedFreeFiber
import Mathlib.AlgebraicTopology.ExtraDegeneracy
import Mathlib.AlgebraicTopology.SimplicialObject.ChainHomotopy

set_option linter.style.header false

/-!
# Section 4: what contractibility of `L` gives after reduced linearization

There are two different chain complexes in the discussion around (4.5):

* `N(L(G,q))`, the normalized Moore complex of the simplicial abelian group
  `L(G,q)`; and
* the alternating face complex of `reducedFree (L(G,q))`, which computes the
  reduced integral homology of the *underlying simplicial set* of `L(G,q)`.

Contractibility of the first complex alone does not formally imply
contractibility or acyclicity of the second: `reducedFree` is nonlinear.  This
file proves the precise bridge that is available in Mathlib.  An extra
degeneracy (hence a genuine simplicial contraction) of `L` is preserved by the
degreewise reduced-free functor, and then Mathlib's extra-degeneracy theorem
contracts the alternating face complex of `reducedFree L`.

The remaining model-specific datum is therefore sharply isolated: construct an
extra degeneracy on the zero augmentation of the explicit Dold--Kan object
`Γ(diskComplex G (q+1))`.  The already formalized chain contraction of
`N(L(G,q+1))` is intentionally not used as a substitute for that datum.
-/

noncomputable section

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits ZeroObject
open SimplicialObject.Augmented

namespace GeneralSphereT.StandardModels

open PathAlgebra

universe u

/-! ## The reduced-free functor before degreewise application -/

/-- Reduced integral distributions as a functor on abelian groups.

The existing `reducedFree` is its degreewise application to a simplicial
abelian group.  Packaging the underlying functor is what lets us use
`ExtraDegeneracy.map`. -/
def reducedFreeBaseFunctor :
    CategoryTheory.Functor AddCommGrpCat.{u} AddCommGrpCat.{u} where
  obj A := AddCommGrpCat.of (RedDist A)
  map f := AddCommGrpCat.ofHom (mapRedDist f.hom).toAddMonoidHom
  map_id A := by
    apply AddCommGrpCat.ext
    intro z
    exact LinearMap.congr_fun mapRedDist_id z
  map_comp f g := by
    apply AddCommGrpCat.ext
    intro z
    change mapRedDist (g.hom.comp f.hom) z =
      mapRedDist g.hom (mapRedDist f.hom z)
    exact (mapRedDist_comp_apply f.hom g.hom z).symm

/-- The directly defined simplicial `reducedFree` is definitionally the
degreewise application of `reducedFreeBaseFunctor`. -/
def reducedFreeIsoWhiskering (A : SimplicialObject AddCommGrpCat.{u}) :
    (((SimplicialObject.whiskering _ _).obj reducedFreeBaseFunctor).obj A) ≅
      reducedFree A :=
  Iso.refl _

/-- Reduced linearization sends the zero homomorphism to the zero
homomorphism.  This is special to the augmentation kernel; it would be false
for the unreduced free-abelian-group functor. -/
@[simp]
theorem reducedFreeBaseFunctor_map_zero (A B : AddCommGrpCat.{u}) :
    reducedFreeBaseFunctor.map (0 : A ⟶ B) = 0 := by
  apply AddCommGrpCat.ext
  intro z
  apply Subtype.ext
  change Finsupp.mapDomain (fun _ : A ↦ (0 : B)) z.1 = 0
  ext b
  by_cases hb : b = 0
  · subst b
    rw [Finsupp.mapDomain]
    have haug : augmentation A z.1 = 0 := LinearMap.mem_ker.mp z.2
    simp only [Finsupp.sum_apply, Finsupp.single_eq_same, Finsupp.zero_apply]
    change z.1.sum (fun _ c ↦ c) = 0
    change z.1.sum (fun _ c ↦ c) = 0 at haug
    exact haug
  · exact Finsupp.mapDomain_of_notMem_range z.1 b (by simp [hb])

/-! ## The augmentation point remains zero after reduced linearization -/

/-- Reduced distributions on a subsingleton abelian group are zero. -/
theorem reducedFreeBaseFunctor_obj_isZero_of_subsingleton
    (A : AddCommGrpCat.{u}) [Subsingleton A] :
    IsZero (reducedFreeBaseFunctor.obj A) := by
  let _ : Unique A := { default := 0, uniq := fun a ↦ Subsingleton.elim a 0 }
  have hz (z : RedDist A) : z = 0 := by
    apply Subtype.ext
    rw [Finsupp.unique_single z.1]
    have haug : augmentation A z.1 = 0 := LinearMap.mem_ker.mp z.2
    rw [Finsupp.unique_single z.1, augmentation_single] at haug
    simp [haug]
  let _ : Subsingleton (RedDist A) :=
    ⟨fun z w ↦ (hz z).trans (hz w).symm⟩
  change IsZero (AddCommGrpCat.of (RedDist A))
  exact AddCommGrpCat.isZero_of_subsingleton _

/-- In particular the image of the categorical zero group is again a zero
object. -/
theorem reducedFreeBaseFunctor_zero_isZero :
    IsZero (reducedFreeBaseFunctor.obj (0 : AddCommGrpCat.{u})) :=
  let _ : Subsingleton (0 : AddCommGrpCat.{u}) :=
    AddCommGrpCat.subsingleton_of_isZero (isZero_zero AddCommGrpCat)
  reducedFreeBaseFunctor_obj_isZero_of_subsingleton _

/-! ## Genuine simplicial contractions survive reduced linearization -/

/-- The weakest contraction datum used below: a combinatorial simplicial
homotopy from the zero endomorphism to the identity. -/
abbrev SimplicialContraction (A : SimplicialObject AddCommGrpCat.{u}) :=
  SimplicialObject.Homotopy (0 : A ⟶ A) (𝟙 A)

/-- Unlike a bare chain contraction of `N(A)`, a simplicial contraction can be
sent through the nonlinear reduced-free functor. -/
def reducedFreeSimplicialContraction
    {A : SimplicialObject AddCommGrpCat.{u}}
    (H : SimplicialContraction A) :
    SimplicialContraction (reducedFree A) := by
  let W := (SimplicialObject.whiskering AddCommGrpCat AddCommGrpCat).obj
    reducedFreeBaseFunctor
  let H' := H.whiskerRight reducedFreeBaseFunctor
  have hzero : W.map (0 : A ⟶ A) = 0 := by
    ext Δ z
    change (reducedFreeBaseFunctor.map
      (0 : A.obj Δ ⟶ A.obj Δ)).hom z = 0
    rw [reducedFreeBaseFunctor_map_zero]
    rfl
  have hid : W.map (𝟙 A) = 𝟙 (W.obj A) := W.map_id A
  rw [hzero, hid] at H'
  exact H'

/-- A genuine simplicial contraction already suffices for reduced integral
acyclicity; an extra degeneracy is only a convenient way to construct such a
contraction. -/
theorem reducedFree_alternating_homology_isZero_of_contraction
    {A : SimplicialObject AddCommGrpCat.{u}}
    (H : SimplicialContraction A) (n : ℕ) :
    IsZero
      ((AlgebraicTopology.AlternatingFaceMapComplex.obj (reducedFree A)).homology n) := by
  change IsZero
    (((AlgebraicTopology.alternatingFaceMapComplex AddCommGrpCat).obj
      (reducedFree A)).homology n)
  let AF := AlgebraicTopology.alternatingFaceMapComplex AddCommGrpCat
  let HF := HomologicalComplex.homologyFunctor AddCommGrpCat
    (ComplexShape.down ℕ) n
  have h := (reducedFreeSimplicialContraction H).map_homology_eq n
  have hz : IsZero (HF.obj (AF.obj (reducedFree A))) := by
    rw [IsZero.iff_id_eq_zero]
    rw [← HF.map_id, ← AF.map_id]
    calc
      HF.map (AF.map (𝟙 (reducedFree A))) = HF.map (AF.map 0) := h.symm
      _ = 0 := by rw [Functor.map_zero, Functor.map_zero]
  simpa only [HF, AF, HomologicalComplex.homologyFunctor_obj] using hz

/-- The contraction-based conclusion bundled as acyclicity. -/
theorem reducedFree_alternating_acyclic_of_contraction
    {A : SimplicialObject AddCommGrpCat.{u}}
    (H : SimplicialContraction A) :
    (AlgebraicTopology.AlternatingFaceMapComplex.obj (reducedFree A)).Acyclic := by
  intro n
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  exact reducedFree_alternating_homology_isZero_of_contraction H n

/-! ## Extra degeneracies survive reduced linearization -/

/-- The zero augmentation of a simplicial abelian group. -/
abbrev zeroAugmentation (A : SimplicialObject AddCommGrpCat.{u}) :
    SimplicialObject.Augmented AddCommGrpCat.{u} :=
  A.augmentOfIsTerminal (isZero_zero AddCommGrpCat).isTerminal

/-- Apply reduced linearization to an extra degeneracy. -/
def reducedFreeExtraDegeneracy
    {A : SimplicialObject AddCommGrpCat.{u}}
    (ed : ExtraDegeneracy (zeroAugmentation A)) :
    ExtraDegeneracy
      (((SimplicialObject.Augmented.whiskering _ _).obj
        reducedFreeBaseFunctor).obj (zeroAugmentation A)) :=
  ed.map reducedFreeBaseFunctor

/-- An extra degeneracy on the zero augmentation supplies the weaker genuine
simplicial contraction datum. -/
def simplicialContractionOfExtraDegeneracy
    {A : SimplicialObject AddCommGrpCat.{u}}
    (ed : ExtraDegeneracy (zeroAugmentation A)) :
    SimplicialContraction A := by
  let H := ed.homotopy
  have hzero : (zeroAugmentation A).hom = 0 := by
    ext Δ : 1
    exact (isZero_zero AddCommGrpCat).eq_of_tgt _ _
  rw [hzero, zero_comp] at H
  exact H

/-- A genuine simplicial contraction of `A` therefore makes the alternating
face complex of `reducedFree A` homotopy equivalent to a complex concentrated
in degree zero at `reducedFreeBaseFunctor.obj 0`. -/
def reducedFreeAlternatingHomotopyEquiv
    {A : SimplicialObject AddCommGrpCat.{u}}
    (ed : ExtraDegeneracy (zeroAugmentation A)) :
    HomotopyEquiv
      (AlgebraicTopology.AlternatingFaceMapComplex.obj (reducedFree A))
      ((ChainComplex.single₀ AddCommGrpCat).obj
        (reducedFreeBaseFunctor.obj (0 : AddCommGrpCat.{u}))) :=
  (reducedFreeExtraDegeneracy ed).homotopyEquiv

/-- Consequently every homology object of the alternating face complex of
`reducedFree A` is zero.  This is the reduced integral acyclicity statement
needed on the left-hand term in (4.5). -/
theorem reducedFree_alternating_homology_isZero
    {A : SimplicialObject AddCommGrpCat.{u}}
    (ed : ExtraDegeneracy (zeroAugmentation A)) (n : ℕ) :
    IsZero
      ((AlgebraicTopology.AlternatingFaceMapComplex.obj (reducedFree A)).homology n) := by
  let e := reducedFreeAlternatingHomotopyEquiv ed
  apply (e.toHomologyIso n).isZero_iff.mpr
  exact (HomologicalComplex.homologyFunctor AddCommGrpCat (ComplexShape.down ℕ) n).map_isZero
    ((ChainComplex.single₀ AddCommGrpCat).map_isZero
      reducedFreeBaseFunctor_zero_isZero)

/-- The same conclusion bundled in Mathlib's chain-complex acyclicity
predicate. -/
theorem reducedFree_alternating_acyclic
    {A : SimplicialObject AddCommGrpCat.{u}}
    (ed : ExtraDegeneracy (zeroAugmentation A)) :
    (AlgebraicTopology.AlternatingFaceMapComplex.obj (reducedFree A)).Acyclic := by
  intro n
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  exact reducedFree_alternating_homology_isZero ed n

/-! ## Specialization to the Dold--Kan path model -/

/-- The exact model-specific input still required for the full topological
form of (4.5): an extra degeneracy on the zero augmentation of the explicit
Dold--Kan disk object. -/
abbrev LExtraDegeneracy (G : AddCommGrpCat.{u}) (q : ℕ) :=
  ExtraDegeneracy (zeroAugmentation (L G (q + 1)))

/-- The minimal version of the missing model-specific input. -/
abbrev LSimplicialContraction (G : AddCommGrpCat.{u}) (q : ℕ) :=
  SimplicialContraction (L G (q + 1))

/-- A genuine simplicial contraction of the Dold--Kan disk object is enough
to prove reduced integral acyclicity. -/
theorem reducedFreeL_alternating_homology_isZero_of_contraction
    (G : AddCommGrpCat.{u}) (q n : ℕ) (H : LSimplicialContraction G q) :
    IsZero
      ((AlgebraicTopology.AlternatingFaceMapComplex.obj
        (reducedFree (L G (q + 1)))).homology n) :=
  reducedFree_alternating_homology_isZero_of_contraction H n

/-- The same minimal-input result in acyclicity form. -/
theorem reducedFreeL_alternating_acyclic_of_contraction
    (G : AddCommGrpCat.{u}) (q : ℕ) (H : LSimplicialContraction G q) :
    (AlgebraicTopology.AlternatingFaceMapComplex.obj
      (reducedFree (L G (q + 1)))).Acyclic :=
  reducedFree_alternating_acyclic_of_contraction H

/-- Once the explicit path-model contraction is supplied, reduced integral
acyclicity of `L(G,q+1)` follows without any further assumption. -/
theorem reducedFreeL_alternating_homology_isZero
    (G : AddCommGrpCat.{u}) (q n : ℕ) (ed : LExtraDegeneracy G q) :
    IsZero
      ((AlgebraicTopology.AlternatingFaceMapComplex.obj
        (reducedFree (L G (q + 1)))).homology n) :=
  reducedFree_alternating_homology_isZero ed n

/-- Acyclicity of the reduced-free path model, in the form directly consumed
by long-exact-homology arguments. -/
theorem reducedFreeL_alternating_acyclic
    (G : AddCommGrpCat.{u}) (q : ℕ) (ed : LExtraDegeneracy G q) :
    (AlgebraicTopology.AlternatingFaceMapComplex.obj
      (reducedFree (L G (q + 1)))).Acyclic :=
  reducedFree_alternating_acyclic ed

/-- For comparison: the normalized Moore complex of `L` is already known to
be contractible from the two-term disk contraction.  This theorem has a
different target from `reducedFreeL_alternating_homology_isZero` and is kept
here to make the distinction machine-visible. -/
theorem normalizedL_homology_isZero_not_reducedFree
    (G : AddCommGrpCat.{u}) (q n : ℕ) :
    IsZero
      ((CategoryTheory.Abelian.DoldKan.N.obj (L G (q + 1))).homology n) :=
  normalizedL_homology_isZero G q n

end GeneralSphereT.StandardModels
