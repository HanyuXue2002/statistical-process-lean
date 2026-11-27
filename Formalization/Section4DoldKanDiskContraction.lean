import Formalization.Section4ReducedFreeContractibility
import Formalization.Section4DoldKanCochainBridge

set_option linter.style.header false

/-!
# Section 4: an explicit contraction of the Dold--Kan disk model

This file works directly with Mathlib's epimorphism-indexed formula for `Γ₀`.
The extra degeneracy of the cochain disk model is obtained by adjoining a new
initial vertex.  On a normalized Dold--Kan summand indexed by
`e : [n] ↠ [r]`, there are two relevant shifted epimorphisms:

* `shift e : [n+1] ↠ [r]`, which prepends `0` (equal to the initial value of
  a monotone surjection); and
* `raise e : [n+1] ↠ [r+1]`, which sends the new vertex to `0` and shifts
  all values of `e` up by one.

For the two-term disk complex, the top summand is sent along `shift`, whereas
the bottom summand is sent along `raise`.  The definitions below isolate the
finite-ordinal combinatorics needed to turn this formula into an
`ExtraDegeneracy`.
-/

noncomputable section

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits Opposite Simplicial
open AlgebraicTopology.DoldKan
open SimplicialObject.Augmented

namespace GeneralSphereT.StandardModels

universe u

namespace DoldKanDiskContraction

open SSet.Augmented.StandardSimplex

/-! ## Shifting epimorphism indices -/

/-- Prepending `0` to a surjection is still surjective. -/
instance shift_epi {n : ℕ} {Δ : SimplexCategory} (e : ⦋n⦌ ⟶ Δ) [Epi e] :
    Epi (shift e) := by
  rw [SimplexCategory.epi_iff_surjective]
  intro y
  have he : Function.Surjective e.toOrderHom :=
    SimplexCategory.epi_iff_surjective.mp (inferInstance : Epi e)
  obtain ⟨x, rfl⟩ := he y
  exact ⟨x.succ, rfl⟩

/-- The codomain-standardized version of a simplex-category morphism. -/
def standardizeCodomain {n : ℕ} {Δ : SimplexCategory} (e : ⦋n⦌ ⟶ Δ) :
    ⦋n⦌ ⟶ ⦋Δ.len⦌ :=
  e ≫ eqToHom (SimplexCategory.mk_len Δ).symm

instance standardizeCodomain_epi {n : ℕ} {Δ : SimplexCategory}
    (e : ⦋n⦌ ⟶ Δ) [Epi e] :
    Epi (standardizeCodomain e) := by
  dsimp [standardizeCodomain]
  infer_instance

@[simp]
theorem standardizeCodomain_eq_self {n r : ℕ} (e : ⦋n⦌ ⟶ ⦋r⦌) :
    standardizeCodomain e = e := by
  change e ≫ 𝟙 _ = e
  simp

/-- Add a new initial value below the codomain of a surjection. -/
def raise {n : ℕ} {Δ : SimplexCategory} (e : ⦋n⦌ ⟶ Δ) :
    ⦋n + 1⦌ ⟶ ⦋Δ.len + 1⦌ :=
  shift (standardizeCodomain e ≫ SimplexCategory.δ 0)

/-- Adding the new initial value makes `raise e` surjective whenever `e` is. -/
instance raise_epi {n : ℕ} {Δ : SimplexCategory} (e : ⦋n⦌ ⟶ Δ) [Epi e] :
    Epi (raise e) := by
  rw [SimplexCategory.epi_iff_surjective]
  intro y
  cases y using Fin.cases with
  | zero => exact ⟨0, by simp [raise, shift]⟩
  | succ y =>
      have he : Function.Surjective e.toOrderHom :=
        SimplexCategory.epi_iff_surjective.mp (inferInstance : Epi e)
      obtain ⟨x, hx⟩ :=
        he ⟨y, by simpa using y.isLt⟩
      refine ⟨x.succ, ?_⟩
      ext
      simpa [raise, shift, standardizeCodomain, SimplexCategory.δ] using
        congrArg Fin.val hx

/-- The summand index obtained by repeating the initial value. -/
def shiftIndex {n : ℕ}
    (A : SimplicialObject.Splitting.IndexSet (op ⦋n⦌)) :
    SimplicialObject.Splitting.IndexSet (op ⦋n + 1⦌) :=
  SimplicialObject.Splitting.IndexSet.mk (shift A.e)

/-- The summand index obtained by adjoining a new initial codomain value. -/
def raiseIndex {n : ℕ}
    (A : SimplicialObject.Splitting.IndexSet (op ⦋n⦌)) :
    SimplicialObject.Splitting.IndexSet (op ⦋n + 1⦌) :=
  SimplicialObject.Splitting.IndexSet.mk (raise A.e)

@[simp]
theorem shiftIndex_len {n : ℕ}
    (A : SimplicialObject.Splitting.IndexSet (op ⦋n⦌)) :
    (shiftIndex A).1.unop.len = A.1.unop.len :=
  rfl

@[simp]
theorem raiseIndex_len {n : ℕ}
    (A : SimplicialObject.Splitting.IndexSet (op ⦋n⦌)) :
    (raiseIndex A).1.unop.len = A.1.unop.len + 1 :=
  rfl

@[simp]
theorem δ_zero_comp_shift {n : ℕ} {Δ : SimplexCategory} (e : ⦋n⦌ ⟶ Δ) :
    SimplexCategory.δ 0 ≫ shift e = e := by
  ext x
  rfl

theorem δ_zero_comp_raise {n : ℕ} {Δ : SimplexCategory} (e : ⦋n⦌ ⟶ Δ) :
    SimplexCategory.δ 0 ≫ raise e =
      standardizeCodomain e ≫ SimplexCategory.δ 0 := by
  ext x
  rfl

/-- Prepending an initial vertex commutes with every noninitial face. -/
theorem δ_succ_comp_shift {n : ℕ} {Δ : SimplexCategory}
    (e : ⦋n + 1⦌ ⟶ Δ) (i : Fin (n + 2)) :
    SimplexCategory.δ i.succ ≫ shift e =
      shift (SimplexCategory.δ i ≫ e) := by
  ext x
  cases x using Fin.cases with
  | zero => rfl
  | succ x =>
      dsimp [shift, SimplexCategory.δ]
      simp [shiftFun, OrderHom.comp_coe, Function.comp_apply,
        Fin.succ_succAbove_succ]
      change (shiftFun e.toOrderHom (i.succAbove x).succ).val =
        (e.toOrderHom (i.succAbove x)).val
      rfl

/-- The raised-index construction commutes with every noninitial face. -/
theorem δ_succ_comp_raise {n : ℕ} {Δ : SimplexCategory}
    (e : ⦋n + 1⦌ ⟶ Δ) (i : Fin (n + 2)) :
    SimplexCategory.δ i.succ ≫ raise e =
      raise (SimplexCategory.δ i ≫ e) := by
  ext x
  cases x using Fin.cases with
  | zero => rfl
  | succ x =>
      dsimp [raise, shift, standardizeCodomain, SimplexCategory.δ]
      simp [shiftFun, OrderHom.comp_coe, Function.comp_apply,
        Fin.succ_succAbove_succ]

/-! The next identities describe how the two index operations interact with
the mono part of an epi--mono factorization. -/

/-- `shift` commutes with a postcomposition which preserves the initial
vertex. -/
theorem shift_comp_of_map_zero {n r : ℕ} {Δ : SimplexCategory}
    (e : ⦋n⦌ ⟶ ⦋r⦌) (m : ⦋r⦌ ⟶ Δ) (hm : m.toOrderHom 0 = 0) :
    shift (e ≫ m) = shift e ≫ m := by
  ext x
  cases x using Fin.cases with
  | zero => exact congrArg Fin.val hm.symm
  | succ x => rfl

/-- Postcomposition with the initial coface changes `shift` into `raise`. -/
theorem shift_comp_δ_zero {n r : ℕ} (e : ⦋n⦌ ⟶ ⦋r⦌) :
    shift (e ≫ SimplexCategory.δ 0) = raise e := by
  rw [raise, standardizeCodomain_eq_self]

/-- Raising a coface increments its index. -/
theorem raise_δ {r : ℕ} (j : Fin (r + 2)) :
    raise (SimplexCategory.δ j) = SimplexCategory.δ j.succ := by
  ext x
  cases x using Fin.cases with
  | zero => rfl
  | succ x =>
      dsimp [raise, shift, standardizeCodomain, SimplexCategory.δ]
      simp only [OrderHom.comp_coe, OrderEmbedding.toOrderHom_coe,
        Function.comp_apply, Fin.succAboveOrderEmb_apply,
        Fin.succ_succAbove_succ, OrderHom.coe_mk, shiftFun_succ]
      simpa using Fin.zero_succAbove (j.succAbove x)

/-- `raise` is compatible with postcomposition between standard simplices. -/
theorem raise_comp {n r s : ℕ} (e : ⦋n⦌ ⟶ ⦋r⦌) (m : ⦋r⦌ ⟶ ⦋s⦌) :
    raise (e ≫ m) = raise e ≫ raise m := by
  ext x
  cases x using Fin.cases with
  | zero => rfl
  | succ x =>
      dsimp [raise, shift, standardizeCodomain, SimplexCategory.δ]
      simp only [OrderHom.comp_coe, OrderEmbedding.toOrderHom_coe,
        Function.comp_apply, Fin.succAboveOrderEmb_apply,
        Fin.succ_succAbove_succ, OrderHom.coe_mk, shiftFun_succ]
      simp [Fin.zero_succAbove, shiftFun]

/-- Removing one point from the source of a monotone surjection either leaves
it surjective, or removes exactly one value from the target.  This is the
epi--mono factorization dichotomy needed for all noninitial face identities. -/
theorem epi_comp_face_or_factor_δ {n r : ℕ} (e : ⦋n + 1⦌ ⟶ ⦋r⦌) [Epi e]
    (i : Fin (n + 2)) :
    Epi (SimplexCategory.δ i ≫ e) ∨
      ∃ (k : ℕ) (h : r = k + 1),
        ∃ (j : Fin (k + 2)) (e' : ⦋n⦌ ⟶ ⦋k⦌),
          Epi e' ∧ e' ≫ SimplexCategory.δ j ≫ eqToHom (by rw [h]) =
            SimplexCategory.δ i ≫ e := by
  let f := SimplexCategory.δ i ≫ e
  by_cases hf : Function.Surjective f.toOrderHom
  · left
    rw [SimplexCategory.epi_iff_surjective]
    exact hf
  · right
    rcases r with _ | k
    · exfalso
      apply hf
      intro y
      refine ⟨0, ?_⟩
      fin_cases y
      exact Fin.eq_zero _
    · rw [Function.Surjective] at hf
      obtain ⟨j, hj'⟩ := not_forall.mp hf
      have hj : ∀ x, f.toOrderHom x ≠ j := by
        intro x hx
        exact hj' ⟨x, hx⟩
      have hesurj : Function.Surjective e.toOrderHom :=
        SimplexCategory.epi_iff_surjective.mp (inferInstance : Epi e)
      obtain ⟨xj, hxj⟩ := hesurj j
      have hxj_eq : xj = i := by
        by_contra hne
        obtain ⟨z, hz⟩ := Fin.exists_succAbove_eq hne
        apply hj z
        change e.toOrderHom (i.succAbove z) = j
        rw [hz, hxj]
      have hei : e.toOrderHom i = j := by
        rw [← hxj_eq, hxj]
      obtain ⟨e', hfac⟩ :=
        SimplexCategory.eq_comp_δ_of_not_surjective' f j hj
      have he' : Epi e' := by
        rw [SimplexCategory.epi_iff_surjective]
        intro z
        let y : Fin (k + 2) := j.succAbove z
        obtain ⟨x, hx⟩ := hesurj y
        have hxi : x ≠ i := by
          intro h
          subst x
          exact Fin.ne_succAbove j z (hei.symm.trans hx)
        obtain ⟨w, hw⟩ := Fin.exists_succAbove_eq hxi
        refine ⟨w, ?_⟩
        have hfacw := congrArg (fun g : ⦋n⦌ ⟶ ⦋k + 1⦌ =>
          g.toOrderHom w) hfac
        have hδ :
            (SimplexCategory.δ j).toOrderHom (e'.toOrderHom w) =
              (SimplexCategory.δ j).toOrderHom z := by
          calc
            _ = f.toOrderHom w := hfacw.symm
            _ = e.toOrderHom (i.succAbove w) := rfl
            _ = e.toOrderHom x := by rw [hw]
            _ = y := hx
            _ = (SimplexCategory.δ j).toOrderHom z := rfl
        exact (SimplexCategory.mono_iff_injective.mp
          (inferInstance : Mono (SimplexCategory.δ j))) hδ
      refine ⟨k, rfl, j, e', he', ?_⟩
      simpa using hfac.symm

@[simp]
theorem mk_standardizeCodomain {n : ℕ}
    (A : SimplicialObject.Splitting.IndexSet (op ⦋n⦌)) :
    SimplicialObject.Splitting.IndexSet.mk (standardizeCodomain A.e) = A := by
  rcases A with ⟨Δ, ⟨e, he⟩⟩
  obtain ⟨Δ⟩ := Δ
  obtain ⟨r⟩ := Δ
  refine SimplicialObject.Splitting.IndexSet.ext
    (SimplicialObject.Splitting.IndexSet.mk (standardizeCodomain e))
    ⟨op ⦋r⦌, ⟨e, he⟩⟩ rfl ?_
  change (e ≫ 𝟙 _) ≫ 𝟙 _ = e
  simp

@[simp]
theorem mk_e {n : ℕ}
    (A : SimplicialObject.Splitting.IndexSet (op ⦋n⦌)) :
    SimplicialObject.Splitting.IndexSet.mk A.e = A := by
  rcases A with ⟨Δ, ⟨e, he⟩⟩
  obtain ⟨Δ⟩ := Δ
  obtain ⟨r⟩ := Δ
  refine SimplicialObject.Splitting.IndexSet.ext
    (SimplicialObject.Splitting.IndexSet.mk e)
    ⟨op ⦋r⦌, ⟨e, he⟩⟩ rfl ?_
  change e ≫ 𝟙 _ = e
  simp

/-! ## The extra-degeneracy operator on `Γ` -/

/-- On a Dold--Kan summand in degree `r`, the extra degeneracy has two terms.
The `d h` part stays in degree `r` and is inserted at `shiftIndex`; the
contracting operator `h` raises the chain degree and is inserted at
`raiseIndex`. -/
def diskExtraS (G : AddCommGrpCat.{u}) (q n : ℕ) :
    (Γ₀.obj (diskSuccComplex G q)).obj (op ⦋n⦌) ⟶
      (Γ₀.obj (diskSuccComplex G q)).obj (op ⦋n + 1⦌) :=
  (Γ₀.splitting (diskSuccComplex G q)).desc (op ⦋n⦌) fun A =>
    dNext A.1.unop.len (diskContractingHom G q) ≫
        ((Γ₀.splitting (diskSuccComplex G q)).cofan
          (op ⦋n + 1⦌)).inj (shiftIndex A) +
      diskContractingHom G q A.1.unop.len (A.1.unop.len + 1) ≫
        ((Γ₀.splitting (diskSuccComplex G q)).cofan
          (op ⦋n + 1⦌)).inj (raiseIndex A)

/-- Formula for `diskExtraS` on one source summand. -/
@[reassoc]
theorem cofan_inj_diskExtraS (G : AddCommGrpCat.{u}) (q n : ℕ)
    (A : SimplicialObject.Splitting.IndexSet (op ⦋n⦌)) :
    ((Γ₀.splitting (diskSuccComplex G q)).cofan
        (op ⦋n⦌)).inj A ≫ diskExtraS G q n =
      dNext A.1.unop.len (diskContractingHom G q) ≫
          ((Γ₀.splitting (diskSuccComplex G q)).cofan
            (op ⦋n + 1⦌)).inj (shiftIndex A) +
        diskContractingHom G q A.1.unop.len (A.1.unop.len + 1) ≫
          ((Γ₀.splitting (diskSuccComplex G q)).cofan
            (op ⦋n + 1⦌)).inj (raiseIndex A) := by
  exact (Γ₀.splitting (diskSuccComplex G q)).ι_desc
    (op ⦋n⦌) _ A

/-! ## The first extra-degeneracy identity -/

set_option backward.isDefEq.respectTransparency false in
theorem diskExtraS_comp_δ_zero (G : AddCommGrpCat.{u}) (q n : ℕ) :
    diskExtraS G q n ≫
        (Γ₀.obj (diskSuccComplex G q)).map (SimplexCategory.δ 0).op = 𝟙 _ := by
  apply (Γ₀.splitting (diskSuccComplex G q)).hom_ext'
  rintro ⟨⟨⟨r⟩⟩, ⟨e, he⟩⟩
  let A : SimplicialObject.Splitting.IndexSet (op ⦋n⦌) :=
    ⟨op ⦋r⦌, ⟨e, he⟩⟩
  change
    ((Γ₀.splitting (diskSuccComplex G q)).cofan
        (op ⦋n⦌)).inj A ≫
        (diskExtraS G q n ≫
          (Γ₀.obj (diskSuccComplex G q)).map (SimplexCategory.δ 0).op) =
      ((Γ₀.splitting (diskSuccComplex G q)).cofan
        (op ⦋n⦌)).inj A ≫ 𝟙 _
  rw [← Category.assoc, cofan_inj_diskExtraS, Preadditive.add_comp]
  simp only [Category.assoc]
  have hshift :
      ((Γ₀.splitting (diskSuccComplex G q)).cofan
          (op ⦋n + 1⦌)).inj (shiftIndex A) ≫
          (Γ₀.obj (diskSuccComplex G q)).map (SimplexCategory.δ 0).op =
        Γ₀.Obj.Termwise.mapMono (diskSuccComplex G q) (𝟙 A.1.unop) ≫
          ((Γ₀.splitting (diskSuccComplex G q)).cofan
            (op ⦋n⦌)).inj A := by
    simpa only [A, SimplicialObject.Splitting.IndexSet.e,
      SimplicialObject.Splitting.IndexSet.mk] using
      Γ₀.Obj.map_on_summand (diskSuccComplex G q) (shiftIndex A)
        (SimplexCategory.δ 0).op
        (e := A.e) (i := 𝟙 A.1.unop) (by
          change A.e ≫ 𝟙 _ = SimplexCategory.δ 0 ≫ shift A.e
          rw [comp_id]
          exact (δ_zero_comp_shift A.e).symm)
  have hraise :
      ((Γ₀.splitting (diskSuccComplex G q)).cofan
          (op ⦋n + 1⦌)).inj (raiseIndex A) ≫
          (Γ₀.obj (diskSuccComplex G q)).map (SimplexCategory.δ 0).op =
        Γ₀.Obj.Termwise.mapMono (diskSuccComplex G q)
            (SimplexCategory.δ 0) ≫
          ((Γ₀.splitting (diskSuccComplex G q)).cofan
            (op ⦋n⦌)).inj A := by
    simpa only [A, standardizeCodomain_eq_self,
      SimplicialObject.Splitting.IndexSet.e,
      SimplicialObject.Splitting.IndexSet.mk] using
      Γ₀.Obj.map_on_summand (diskSuccComplex G q) (raiseIndex A)
        (SimplexCategory.δ 0).op
        (e := A.e) (i := SimplexCategory.δ 0)
        (by
          change A.e ≫ SimplexCategory.δ 0 =
            SimplexCategory.δ 0 ≫ raise A.e
          rw [δ_zero_comp_raise, standardizeCodomain_eq_self])
  rw [hshift, hraise]
  simp only [Γ₀.Obj.Termwise.mapMono_id, id_comp, comp_id]
  rw [Γ₀.Obj.Termwise.mapMono_δ₀]
  rw [← Category.assoc]
  rw [← Preadditive.add_comp]
  change
    (dNext r (diskContractingHom G q) +
      diskContractingHom G q r (r + 1) ≫
        (diskSuccComplex G q).d (r + 1) r) ≫
      ((Γ₀.splitting (diskSuccComplex G q)).cofan
        (op ⦋n⦌)).inj A = _
  rw [← prevD_eq (diskContractingHom G q) (show
    (ComplexShape.down ℕ).Rel (r + 1) r by
      rw [ComplexShape.down_Rel])]
  change
    (Homotopy.nullHomotopicMap (diskContractingHom G q)).f r ≫
      ((Γ₀.splitting (diskSuccComplex G q)).cofan
        (op ⦋n⦌)).inj A = _
  rw [diskNullHomotopicMap_eq_id]
  simp

/-! ## The degree-zero boundary identity -/

set_option backward.isDefEq.respectTransparency false in
/-- The extra operator in simplicial degree zero vanishes after the other
face.  This is the endpoint identity required by an extra degeneracy over the
zero augmentation. -/
theorem diskExtraS_zero_comp_δ_one (G : AddCommGrpCat.{u}) (q : ℕ) :
    diskExtraS G q 0 ≫
      (Γ₀.obj (diskSuccComplex G q)).map (SimplexCategory.δ 1).op = 0 := by
  apply (Γ₀.splitting (diskSuccComplex G q)).hom_ext'
  rintro ⟨⟨⟨r⟩⟩, ⟨e, he⟩⟩
  have hr : r = 0 := by
    have : r ≤ 0 := by
      simpa only [unop_op, SimplexCategory.len_mk] using
        SimplexCategory.len_le_of_epi e
    omega
  subst r
  have heq : e = 𝟙 ⦋0⦌ := Subsingleton.elim _ _
  subst e
  let A : SimplicialObject.Splitting.IndexSet (op ⦋0⦌) :=
    ⟨op ⦋0⦌, ⟨𝟙 ⦋0⦌, he⟩⟩
  change
    ((Γ₀.splitting (diskSuccComplex G q)).cofan
        (op ⦋0⦌)).inj A ≫
        (diskExtraS G q 0 ≫
          (Γ₀.obj (diskSuccComplex G q)).map
            (SimplexCategory.δ 1).op) = 0
  rw [← Category.assoc, cofan_inj_diskExtraS, Preadditive.add_comp]
  simp only [Category.assoc]
  have hshift :
      ((Γ₀.splitting (diskSuccComplex G q)).cofan
          (op ⦋1⦌)).inj (shiftIndex A) ≫
          (Γ₀.obj (diskSuccComplex G q)).map
            (SimplexCategory.δ 1).op =
        Γ₀.Obj.Termwise.mapMono (diskSuccComplex G q) (𝟙 ⦋0⦌) ≫
          ((Γ₀.splitting (diskSuccComplex G q)).cofan
            (op ⦋0⦌)).inj A := by
    simpa only [A, SimplicialObject.Splitting.IndexSet.e,
      SimplicialObject.Splitting.IndexSet.mk] using
      Γ₀.Obj.map_on_summand (diskSuccComplex G q) (shiftIndex A)
        (SimplexCategory.δ 1).op
        (e := 𝟙 ⦋0⦌) (i := 𝟙 ⦋0⦌) (by
          ext x
          fin_cases x
          rfl)
  have hraise :
      ((Γ₀.splitting (diskSuccComplex G q)).cofan
          (op ⦋1⦌)).inj (raiseIndex A) ≫
          (Γ₀.obj (diskSuccComplex G q)).map
            (SimplexCategory.δ 1).op =
        Γ₀.Obj.Termwise.mapMono (diskSuccComplex G q)
            (SimplexCategory.δ 1) ≫
          ((Γ₀.splitting (diskSuccComplex G q)).cofan
            (op ⦋0⦌)).inj A := by
    simpa only [A, SimplicialObject.Splitting.IndexSet.e,
      SimplicialObject.Splitting.IndexSet.mk] using
      Γ₀.Obj.map_on_summand (diskSuccComplex G q) (raiseIndex A)
        (SimplexCategory.δ 1).op
        (e := 𝟙 ⦋0⦌) (i := SimplexCategory.δ 1) (by
          ext x
          fin_cases x
          rfl)
  have hδ_one :
      Γ₀.Obj.Termwise.mapMono (diskSuccComplex G q)
        (SimplexCategory.δ (1 : Fin 2)) = 0 := by
    apply Γ₀.Obj.Termwise.mapMono_eq_zero
    · intro h
      have hlen := congrArg SimplexCategory.len h
      simp at hlen
    · rw [Isδ₀.iff]
      simp
  have hdNext : dNext 0 (diskContractingHom G q) = 0 := by
    rw [dNext_nat]
    simp
  rw [hshift, hraise]
  simp only [Γ₀.Obj.Termwise.mapMono_id, id_comp, hδ_one, zero_comp,
    comp_zero, add_zero]
  change dNext 0 (diskContractingHom G q) ≫
    ((Γ₀.splitting (diskSuccComplex G q)).cofan (op ⦋0⦌)).inj A = 0
  rw [hdNext, zero_comp]

/-! ## Noninitial faces: the surjective branch -/

set_option backward.isDefEq.respectTransparency false in
/-- Face naturality on a summand when deleting the vertex leaves its epi
index surjective.  In this branch the epi--mono factorization has identity
mono part, and both `shift` and `raise` simply commute with the face. -/
theorem cofan_inj_diskExtraS_comp_δ_succ_of_epi
    (G : AddCommGrpCat.{u}) (q n r : ℕ) (i : Fin (n + 2))
    (e : ⦋n + 1⦌ ⟶ ⦋r⦌) [Epi e]
    [Epi (SimplexCategory.δ i ≫ e)] :
    ((Γ₀.splitting (diskSuccComplex G q)).cofan
        (op ⦋n + 1⦌)).inj
          (SimplicialObject.Splitting.IndexSet.mk e) ≫
        diskExtraS G q (n + 1) ≫
          (Γ₀.obj (diskSuccComplex G q)).map
            (SimplexCategory.δ i.succ).op =
      ((Γ₀.splitting (diskSuccComplex G q)).cofan
          (op ⦋n + 1⦌)).inj
            (SimplicialObject.Splitting.IndexSet.mk e) ≫
        (Γ₀.obj (diskSuccComplex G q)).map
          (SimplexCategory.δ i).op ≫ diskExtraS G q n := by
  let A : SimplicialObject.Splitting.IndexSet (op ⦋n + 1⦌) :=
    SimplicialObject.Splitting.IndexSet.mk e
  let f : ⦋n⦌ ⟶ ⦋r⦌ := SimplexCategory.δ i ≫ e
  let B : SimplicialObject.Splitting.IndexSet (op ⦋n⦌) :=
    SimplicialObject.Splitting.IndexSet.mk f
  change
    ((Γ₀.splitting (diskSuccComplex G q)).cofan
        (op ⦋n + 1⦌)).inj A ≫ diskExtraS G q (n + 1) ≫
          (Γ₀.obj (diskSuccComplex G q)).map
            (SimplexCategory.δ i.succ).op =
      ((Γ₀.splitting (diskSuccComplex G q)).cofan
        (op ⦋n + 1⦌)).inj A ≫
          (Γ₀.obj (diskSuccComplex G q)).map
            (SimplexCategory.δ i).op ≫ diskExtraS G q n
  have hface :
      ((Γ₀.splitting (diskSuccComplex G q)).cofan
          (op ⦋n + 1⦌)).inj A ≫
          (Γ₀.obj (diskSuccComplex G q)).map
            (SimplexCategory.δ i).op =
        Γ₀.Obj.Termwise.mapMono (diskSuccComplex G q) (𝟙 ⦋r⦌) ≫
          ((Γ₀.splitting (diskSuccComplex G q)).cofan
            (op ⦋n⦌)).inj B := by
    simpa only [A, B, f, SimplicialObject.Splitting.IndexSet.e,
      SimplicialObject.Splitting.IndexSet.mk] using
      Γ₀.Obj.map_on_summand (diskSuccComplex G q) A
        (SimplexCategory.δ i).op (e := f) (i := 𝟙 ⦋r⦌) (by
          change f ≫ 𝟙 ⦋r⦌ = SimplexCategory.δ i ≫ e
          simp [f])
  have hshift :
      ((Γ₀.splitting (diskSuccComplex G q)).cofan
          (op ⦋(n + 1) + 1⦌)).inj (shiftIndex A) ≫
          (Γ₀.obj (diskSuccComplex G q)).map
            (SimplexCategory.δ i.succ).op =
        Γ₀.Obj.Termwise.mapMono (diskSuccComplex G q) (𝟙 ⦋r⦌) ≫
          ((Γ₀.splitting (diskSuccComplex G q)).cofan
            (op ⦋n + 1⦌)).inj (shiftIndex B) := by
    simpa only [A, B, f, shiftIndex,
      SimplicialObject.Splitting.IndexSet.e,
      SimplicialObject.Splitting.IndexSet.mk] using
      Γ₀.Obj.map_on_summand (diskSuccComplex G q) (shiftIndex A)
        (SimplexCategory.δ i.succ).op
        (e := shift f) (i := 𝟙 ⦋r⦌) (by
          change shift f ≫ 𝟙 ⦋r⦌ =
            SimplexCategory.δ i.succ ≫ shift e
          rw [comp_id, δ_succ_comp_shift]
          )
  have hraise :
      ((Γ₀.splitting (diskSuccComplex G q)).cofan
          (op ⦋(n + 1) + 1⦌)).inj (raiseIndex A) ≫
          (Γ₀.obj (diskSuccComplex G q)).map
            (SimplexCategory.δ i.succ).op =
        Γ₀.Obj.Termwise.mapMono (diskSuccComplex G q)
            (𝟙 ⦋r + 1⦌) ≫
          ((Γ₀.splitting (diskSuccComplex G q)).cofan
            (op ⦋n + 1⦌)).inj (raiseIndex B) := by
    simpa only [A, B, f, raiseIndex,
      SimplicialObject.Splitting.IndexSet.e,
      SimplicialObject.Splitting.IndexSet.mk] using
      Γ₀.Obj.map_on_summand (diskSuccComplex G q) (raiseIndex A)
        (SimplexCategory.δ i.succ).op
        (e := raise f) (i := 𝟙 ⦋r + 1⦌) (by
          change raise f ≫ 𝟙 ⦋r + 1⦌ =
            SimplexCategory.δ i.succ ≫ raise e
          rw [comp_id, δ_succ_comp_raise]
          )
  rw [← Category.assoc, cofan_inj_diskExtraS, Preadditive.add_comp]
  simp only [Category.assoc]
  rw [hshift, hraise]
  simp only [Γ₀.Obj.Termwise.mapMono_id, id_comp]
  rw [← Category.assoc, hface]
  simp only [Γ₀.Obj.Termwise.mapMono_id, id_comp]
  change
    dNext r (diskContractingHom G q) ≫
          ((Γ₀.splitting (diskSuccComplex G q)).cofan
            (op ⦋n + 1⦌)).inj (shiftIndex B) +
        diskContractingHom G q r (r + 1) ≫
          ((Γ₀.splitting (diskSuccComplex G q)).cofan
            (op ⦋n + 1⦌)).inj (raiseIndex B) =
      ((Γ₀.splitting (diskSuccComplex G q)).cofan
        (op ⦋n⦌)).inj B ≫ diskExtraS G q n
  exact (cofan_inj_diskExtraS G q n B).symm

/-! ## Noninitial faces: a noninitial value is lost -/

set_option backward.isDefEq.respectTransparency false in
/-- If the deleted source vertex was the unique preimage of a nonzero target
value, the mono part of the factorization is `δ j` with `j ≠ 0`.  Every
termwise map on both sides is then zero. -/
theorem cofan_inj_diskExtraS_comp_δ_succ_of_factor_δ_ne_zero
    (G : AddCommGrpCat.{u}) (q n k : ℕ) (i : Fin (n + 2))
    (j : Fin (k + 2)) (hj : j ≠ 0)
    (e : ⦋n + 1⦌ ⟶ ⦋k + 1⦌) [Epi e]
    (e' : ⦋n⦌ ⟶ ⦋k⦌) [Epi e']
    (fac : e' ≫ SimplexCategory.δ j = SimplexCategory.δ i ≫ e) :
    ((Γ₀.splitting (diskSuccComplex G q)).cofan
        (op ⦋n + 1⦌)).inj
          (SimplicialObject.Splitting.IndexSet.mk e) ≫
        diskExtraS G q (n + 1) ≫
          (Γ₀.obj (diskSuccComplex G q)).map
            (SimplexCategory.δ i.succ).op =
      ((Γ₀.splitting (diskSuccComplex G q)).cofan
          (op ⦋n + 1⦌)).inj
            (SimplicialObject.Splitting.IndexSet.mk e) ≫
        (Γ₀.obj (diskSuccComplex G q)).map
          (SimplexCategory.δ i).op ≫ diskExtraS G q n := by
  let A : SimplicialObject.Splitting.IndexSet (op ⦋n + 1⦌) :=
    SimplicialObject.Splitting.IndexSet.mk e
  let B : SimplicialObject.Splitting.IndexSet (op ⦋n⦌) :=
    SimplicialObject.Splitting.IndexSet.mk e'
  change
    ((Γ₀.splitting (diskSuccComplex G q)).cofan
        (op ⦋n + 1⦌)).inj A ≫ diskExtraS G q (n + 1) ≫
          (Γ₀.obj (diskSuccComplex G q)).map
            (SimplexCategory.δ i.succ).op =
      ((Γ₀.splitting (diskSuccComplex G q)).cofan
        (op ⦋n + 1⦌)).inj A ≫
          (Γ₀.obj (diskSuccComplex G q)).map
            (SimplexCategory.δ i).op ≫ diskExtraS G q n
  have hface :
      ((Γ₀.splitting (diskSuccComplex G q)).cofan
          (op ⦋n + 1⦌)).inj A ≫
          (Γ₀.obj (diskSuccComplex G q)).map
            (SimplexCategory.δ i).op =
        Γ₀.Obj.Termwise.mapMono (diskSuccComplex G q)
            (SimplexCategory.δ j) ≫
          ((Γ₀.splitting (diskSuccComplex G q)).cofan
            (op ⦋n⦌)).inj B := by
    simpa only [A, B, SimplicialObject.Splitting.IndexSet.e,
      SimplicialObject.Splitting.IndexSet.mk] using
      Γ₀.Obj.map_on_summand (diskSuccComplex G q) A
        (SimplexCategory.δ i).op (e := e')
          (i := SimplexCategory.δ j) fac
  have hshift :
      ((Γ₀.splitting (diskSuccComplex G q)).cofan
          (op ⦋(n + 1) + 1⦌)).inj (shiftIndex A) ≫
          (Γ₀.obj (diskSuccComplex G q)).map
            (SimplexCategory.δ i.succ).op =
        Γ₀.Obj.Termwise.mapMono (diskSuccComplex G q)
            (SimplexCategory.δ j) ≫
          ((Γ₀.splitting (diskSuccComplex G q)).cofan
            (op ⦋n + 1⦌)).inj (shiftIndex B) := by
    simpa only [A, B, shiftIndex,
      SimplicialObject.Splitting.IndexSet.e,
      SimplicialObject.Splitting.IndexSet.mk] using
      Γ₀.Obj.map_on_summand (diskSuccComplex G q) (shiftIndex A)
        (SimplexCategory.δ i.succ).op
        (e := shift e') (i := SimplexCategory.δ j) (by
          change shift e' ≫ SimplexCategory.δ j =
            SimplexCategory.δ i.succ ≫ shift e
          rw [δ_succ_comp_shift, ← fac,
            shift_comp_of_map_zero e' (SimplexCategory.δ j)]
          exact Fin.succAbove_ne_zero_zero hj)
  have hraise :
      ((Γ₀.splitting (diskSuccComplex G q)).cofan
          (op ⦋(n + 1) + 1⦌)).inj (raiseIndex A) ≫
          (Γ₀.obj (diskSuccComplex G q)).map
            (SimplexCategory.δ i.succ).op =
        Γ₀.Obj.Termwise.mapMono (diskSuccComplex G q)
            (SimplexCategory.δ j.succ) ≫
          ((Γ₀.splitting (diskSuccComplex G q)).cofan
            (op ⦋n + 1⦌)).inj (raiseIndex B) := by
    simpa only [A, B, raiseIndex,
      SimplicialObject.Splitting.IndexSet.e,
      SimplicialObject.Splitting.IndexSet.mk] using
      Γ₀.Obj.map_on_summand (diskSuccComplex G q) (raiseIndex A)
        (SimplexCategory.δ i.succ).op
        (e := raise e') (i := SimplexCategory.δ j.succ) (by
          change raise e' ≫ SimplexCategory.δ j.succ =
            SimplexCategory.δ i.succ ≫ raise e
          rw [δ_succ_comp_raise, ← fac, raise_comp, raise_δ])
  have hmap_j :
      Γ₀.Obj.Termwise.mapMono (diskSuccComplex G q)
        (SimplexCategory.δ j) = 0 := by
    apply Γ₀.Obj.Termwise.mapMono_eq_zero
    · intro h
      have hlen := congrArg SimplexCategory.len h
      simp at hlen
    · rw [Isδ₀.iff]
      exact hj
  have hmap_succ :
      Γ₀.Obj.Termwise.mapMono (diskSuccComplex G q)
        (SimplexCategory.δ j.succ) = 0 := by
    apply Γ₀.Obj.Termwise.mapMono_eq_zero
    · intro h
      have hlen := congrArg SimplexCategory.len h
      simp at hlen
    · rw [Isδ₀.iff]
      exact Fin.succ_ne_zero j
  rw [← Category.assoc, cofan_inj_diskExtraS, Preadditive.add_comp]
  simp only [Category.assoc]
  rw [hshift, hraise, hmap_j, hmap_succ]
  simp only [zero_comp, comp_zero, add_zero]
  rw [← Category.assoc, hface, hmap_j]
  simp

/-! ## Noninitial faces: the initial value is lost -/

set_option backward.isDefEq.respectTransparency false in
/-- If the removed source vertex was the unique preimage of `0`, the mono
part is `δ 0`.  The shifted summand becomes the raised summand, and the two
remaining coefficient identities are `d² = 0` and the defining formula for
`dNext`. -/
theorem cofan_inj_diskExtraS_comp_δ_succ_of_factor_δ_zero
    (G : AddCommGrpCat.{u}) (q n k : ℕ) (i : Fin (n + 2))
    (e : ⦋n + 1⦌ ⟶ ⦋k + 1⦌) [Epi e]
    (e' : ⦋n⦌ ⟶ ⦋k⦌) [Epi e']
    (fac : e' ≫ SimplexCategory.δ 0 = SimplexCategory.δ i ≫ e) :
    ((Γ₀.splitting (diskSuccComplex G q)).cofan
        (op ⦋n + 1⦌)).inj
          (SimplicialObject.Splitting.IndexSet.mk e) ≫
        diskExtraS G q (n + 1) ≫
          (Γ₀.obj (diskSuccComplex G q)).map
            (SimplexCategory.δ i.succ).op =
      ((Γ₀.splitting (diskSuccComplex G q)).cofan
          (op ⦋n + 1⦌)).inj
            (SimplicialObject.Splitting.IndexSet.mk e) ≫
        (Γ₀.obj (diskSuccComplex G q)).map
          (SimplexCategory.δ i).op ≫ diskExtraS G q n := by
  let A : SimplicialObject.Splitting.IndexSet (op ⦋n + 1⦌) :=
    SimplicialObject.Splitting.IndexSet.mk e
  let B : SimplicialObject.Splitting.IndexSet (op ⦋n⦌) :=
    SimplicialObject.Splitting.IndexSet.mk e'
  change
    ((Γ₀.splitting (diskSuccComplex G q)).cofan
        (op ⦋n + 1⦌)).inj A ≫ diskExtraS G q (n + 1) ≫
          (Γ₀.obj (diskSuccComplex G q)).map
            (SimplexCategory.δ i.succ).op =
      ((Γ₀.splitting (diskSuccComplex G q)).cofan
        (op ⦋n + 1⦌)).inj A ≫
          (Γ₀.obj (diskSuccComplex G q)).map
            (SimplexCategory.δ i).op ≫ diskExtraS G q n
  have hface :
      ((Γ₀.splitting (diskSuccComplex G q)).cofan
          (op ⦋n + 1⦌)).inj A ≫
          (Γ₀.obj (diskSuccComplex G q)).map
            (SimplexCategory.δ i).op =
        Γ₀.Obj.Termwise.mapMono (diskSuccComplex G q)
            (SimplexCategory.δ (0 : Fin (k + 2))) ≫
          ((Γ₀.splitting (diskSuccComplex G q)).cofan
            (op ⦋n⦌)).inj B := by
    simpa only [A, B, SimplicialObject.Splitting.IndexSet.e,
      SimplicialObject.Splitting.IndexSet.mk] using
      Γ₀.Obj.map_on_summand (diskSuccComplex G q) A
        (SimplexCategory.δ i).op (e := e')
          (i := SimplexCategory.δ (0 : Fin (k + 2))) fac
  have hshift :
      ((Γ₀.splitting (diskSuccComplex G q)).cofan
          (op ⦋(n + 1) + 1⦌)).inj (shiftIndex A) ≫
          (Γ₀.obj (diskSuccComplex G q)).map
            (SimplexCategory.δ i.succ).op =
        Γ₀.Obj.Termwise.mapMono (diskSuccComplex G q)
            (𝟙 ⦋k + 1⦌) ≫
          ((Γ₀.splitting (diskSuccComplex G q)).cofan
            (op ⦋n + 1⦌)).inj (raiseIndex B) := by
    simpa only [A, B, shiftIndex, raiseIndex,
      SimplicialObject.Splitting.IndexSet.e,
      SimplicialObject.Splitting.IndexSet.mk] using
      Γ₀.Obj.map_on_summand (diskSuccComplex G q) (shiftIndex A)
        (SimplexCategory.δ i.succ).op
        (e := raise e') (i := 𝟙 ⦋k + 1⦌) (by
          change raise e' ≫ 𝟙 ⦋k + 1⦌ =
            SimplexCategory.δ i.succ ≫ shift e
          rw [comp_id, δ_succ_comp_shift, ← fac, shift_comp_δ_zero])
  have hraise :
      ((Γ₀.splitting (diskSuccComplex G q)).cofan
          (op ⦋(n + 1) + 1⦌)).inj (raiseIndex A) ≫
          (Γ₀.obj (diskSuccComplex G q)).map
            (SimplexCategory.δ i.succ).op =
        Γ₀.Obj.Termwise.mapMono (diskSuccComplex G q)
            (SimplexCategory.δ (1 : Fin (k + 3))) ≫
          ((Γ₀.splitting (diskSuccComplex G q)).cofan
            (op ⦋n + 1⦌)).inj (raiseIndex B) := by
    simpa only [A, B, raiseIndex,
      SimplicialObject.Splitting.IndexSet.e,
      SimplicialObject.Splitting.IndexSet.mk] using
      Γ₀.Obj.map_on_summand (diskSuccComplex G q) (raiseIndex A)
        (SimplexCategory.δ i.succ).op
        (e := raise e')
          (i := SimplexCategory.δ (1 : Fin (k + 3))) (by
            change raise e' ≫ SimplexCategory.δ (1 : Fin (k + 3)) =
              SimplexCategory.δ i.succ ≫ raise e
            rw [δ_succ_comp_raise, ← fac, raise_comp, raise_δ]
            congr 2)
  have hmap_one :
      Γ₀.Obj.Termwise.mapMono (diskSuccComplex G q)
        (SimplexCategory.δ (1 : Fin (k + 3))) = 0 := by
    apply Γ₀.Obj.Termwise.mapMono_eq_zero
    · intro h
      have hlen := congrArg SimplexCategory.len h
      simp at hlen
    · rw [Isδ₀.iff]
      simp
  have hdd :
      (diskSuccComplex G q).d (k + 1) k ≫
        dNext k (diskContractingHom G q) = 0 := by
    rw [dNext_nat]
    simp
  have hdh :
      (diskSuccComplex G q).d (k + 1) k ≫
          diskContractingHom G q k (k + 1) =
        dNext (k + 1) (diskContractingHom G q) := by
    exact (dNext_eq (diskContractingHom G q)
      (show (ComplexShape.down ℕ).Rel (k + 1) k by
        rw [ComplexShape.down_Rel])).symm
  rw [← Category.assoc, cofan_inj_diskExtraS, Preadditive.add_comp]
  simp only [Category.assoc]
  rw [hshift, hraise]
  simp only [Γ₀.Obj.Termwise.mapMono_id, id_comp, hmap_one,
    zero_comp, comp_zero, add_zero]
  rw [← Category.assoc, hface, Γ₀.Obj.Termwise.mapMono_δ₀]
  simp only [Category.assoc]
  rw [cofan_inj_diskExtraS, Preadditive.comp_add]
  change
    dNext (k + 1) (diskContractingHom G q) ≫
        ((Γ₀.splitting (diskSuccComplex G q)).cofan
          (op ⦋n + 1⦌)).inj (raiseIndex B) =
      ((diskSuccComplex G q).d (k + 1) k ≫
          dNext k (diskContractingHom G q)) ≫
            ((Γ₀.splitting (diskSuccComplex G q)).cofan
              (op ⦋n + 1⦌)).inj (shiftIndex B) +
        ((diskSuccComplex G q).d (k + 1) k ≫
          diskContractingHom G q k (k + 1)) ≫
            ((Γ₀.splitting (diskSuccComplex G q)).cofan
              (op ⦋n + 1⦌)).inj (raiseIndex B)
  rw [hdd, hdh]
  simp

/-! ## All noninitial faces -/

set_option backward.isDefEq.respectTransparency false in
/-- The explicit operator satisfies every noninitial face identity. -/
theorem diskExtraS_comp_δ_succ (G : AddCommGrpCat.{u}) (q n : ℕ)
    (i : Fin (n + 2)) :
    diskExtraS G q (n + 1) ≫
        (Γ₀.obj (diskSuccComplex G q)).map
          (SimplexCategory.δ i.succ).op =
      (Γ₀.obj (diskSuccComplex G q)).map
          (SimplexCategory.δ i).op ≫ diskExtraS G q n := by
  apply (Γ₀.splitting (diskSuccComplex G q)).hom_ext'
  rintro ⟨⟨⟨r⟩⟩, ⟨e, he⟩⟩
  rcases epi_comp_face_or_factor_δ e i with hepi | hfactor
  · haveI : Epi (SimplexCategory.δ i ≫ e) := hepi
    simpa only [SimplicialObject.Splitting.IndexSet.mk] using
      cofan_inj_diskExtraS_comp_δ_succ_of_epi G q n r i e
  · obtain ⟨k, hr, j, e', he', fac⟩ := hfactor
    subst r
    simp only [eqToHom_refl, comp_id] at fac
    haveI : Epi e' := he'
    by_cases hj : j = 0
    · subst j
      simpa only [SimplicialObject.Splitting.IndexSet.mk] using
        cofan_inj_diskExtraS_comp_δ_succ_of_factor_δ_zero
          G q n k i e e' fac
    · simpa only [SimplicialObject.Splitting.IndexSet.mk] using
        cofan_inj_diskExtraS_comp_δ_succ_of_factor_δ_ne_zero
          G q n k i j hj e e' fac

/-! ## Direct contraction after reduced linearization

For the alternating face complex, the degeneracy identities are irrelevant:
the three face identities proved above already give a contracting homotopy.
We first apply the reduced-free functor degreewise to the explicit operator.
-/

/-- The explicit disk operator after degreewise reduced linearization. -/
def reducedFreeDiskExtraS (G : AddCommGrpCat.{u}) (q n : ℕ) :
    (reducedFree (L G (q + 1))).obj (op ⦋n⦌) ⟶
      (reducedFree (L G (q + 1))).obj (op ⦋n + 1⦌) :=
  reducedFreeBaseFunctor.map (diskExtraS G q n)

@[reassoc]
theorem reducedFreeDiskExtraS_comp_δ_zero
    (G : AddCommGrpCat.{u}) (q n : ℕ) :
    reducedFreeDiskExtraS G q n ≫
        (reducedFree (L G (q + 1))).δ 0 = 𝟙 _ := by
  change reducedFreeBaseFunctor.map (diskExtraS G q n) ≫
      reducedFreeBaseFunctor.map
        ((Γ₀.obj (diskSuccComplex G q)).map
          (SimplexCategory.δ 0).op) = 𝟙 _
  rw [← reducedFreeBaseFunctor.map_comp, diskExtraS_comp_δ_zero,
    reducedFreeBaseFunctor.map_id]

@[reassoc]
theorem reducedFreeDiskExtraS_zero_comp_δ_one
    (G : AddCommGrpCat.{u}) (q : ℕ) :
    reducedFreeDiskExtraS G q 0 ≫
        (reducedFree (L G (q + 1))).δ 1 = 0 := by
  change reducedFreeBaseFunctor.map (diskExtraS G q 0) ≫
      reducedFreeBaseFunctor.map
        ((Γ₀.obj (diskSuccComplex G q)).map
          (SimplexCategory.δ 1).op) = 0
  rw [← reducedFreeBaseFunctor.map_comp, diskExtraS_zero_comp_δ_one,
    reducedFreeBaseFunctor_map_zero]

@[reassoc]
theorem reducedFreeDiskExtraS_comp_δ_succ
    (G : AddCommGrpCat.{u}) (q n : ℕ) (i : Fin (n + 2)) :
    reducedFreeDiskExtraS G q (n + 1) ≫
        (reducedFree (L G (q + 1))).δ i.succ =
      (reducedFree (L G (q + 1))).δ i ≫
        reducedFreeDiskExtraS G q n := by
  change reducedFreeBaseFunctor.map (diskExtraS G q (n + 1)) ≫
      reducedFreeBaseFunctor.map
        ((Γ₀.obj (diskSuccComplex G q)).map
          (SimplexCategory.δ i.succ).op) =
    reducedFreeBaseFunctor.map
        ((Γ₀.obj (diskSuccComplex G q)).map
          (SimplexCategory.δ i).op) ≫
      reducedFreeBaseFunctor.map (diskExtraS G q n)
  rw [← reducedFreeBaseFunctor.map_comp, diskExtraS_comp_δ_succ,
    reducedFreeBaseFunctor.map_comp]

/-- The alternating face complex of the reduced-free disk model. -/
abbrev reducedFreeLAlternatingComplex (G : AddCommGrpCat.{u}) (q : ℕ) :=
  AlgebraicTopology.AlternatingFaceMapComplex.obj
    (reducedFree (L G (q + 1)))

/-- Direct chain contraction of the alternating face complex.  This is the
standard extra-degeneracy calculation, but it uses only face identities and
therefore does not require proving compatibility with simplicial
degeneracies. -/
noncomputable def reducedFreeLAlternatingContractingHomotopy
    (G : AddCommGrpCat.{u}) (q : ℕ) :
    _root_.Homotopy
      (0 : reducedFreeLAlternatingComplex G q ⟶
        reducedFreeLAlternatingComplex G q)
      (𝟙 (reducedFreeLAlternatingComplex G q)) where
  hom i := Pi.single (i + 1) (-reducedFreeDiskExtraS G q i)
  zero i j hij := Pi.single_eq_of_ne (Ne.symm hij) _
  comm i := by
    cases i with
    | zero =>
      rw [Homotopy.prevD_chainComplex, Homotopy.dNext_zero_chainComplex]
      simp [reducedFreeDiskExtraS_comp_δ_zero,
        reducedFreeDiskExtraS_zero_comp_δ_one]
    | succ i =>
      rw [Homotopy.prevD_chainComplex, Homotopy.dNext_succ_chainComplex]
      simp [Fin.sum_univ_succ (n := i + 2),
        reducedFreeDiskExtraS_comp_δ_zero,
        Preadditive.sum_comp, Preadditive.comp_sum,
        reducedFreeDiskExtraS_comp_δ_succ, pow_succ]

/-- Every homology object of the reduced-free disk's alternating face complex
is zero.  Unlike normalized contractibility of `L`, this is precisely the
reduced integral homology statement about its underlying simplicial set. -/
theorem reducedFreeLAlternating_homology_isZero
    (G : AddCommGrpCat.{u}) (q n : ℕ) :
    IsZero ((reducedFreeLAlternatingComplex G q).homology n) := by
  let C := reducedFreeLAlternatingComplex G q
  let HF := HomologicalComplex.homologyFunctor AddCommGrpCat
    (ComplexShape.down ℕ) n
  have h := (reducedFreeLAlternatingContractingHomotopy G q).homologyMap_eq n
  have hz : IsZero (HF.obj C) := by
    rw [IsZero.iff_id_eq_zero]
    rw [← HF.map_id]
    calc
      HF.map (𝟙 C) = HF.map (0 : C ⟶ C) := h.symm
      _ = 0 := by rw [Functor.map_zero]
  simpa only [C, HF, HomologicalComplex.homologyFunctor_obj] using hz

/-- Unconditional reduced integral acyclicity of the standard Dold--Kan disk
model.  This is the vanishing input required in the long exact sequence for
formula (4.5). -/
theorem reducedFreeLAlternating_acyclic
    (G : AddCommGrpCat.{u}) (q : ℕ) :
    (reducedFreeLAlternatingComplex G q).Acyclic := by
  intro n
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  exact reducedFreeLAlternating_homology_isZero G q n

/-! ## The optional remaining degeneracy identity

The face identities already suffice for the direct chain contraction above.
Only compatibility with simplicial degeneracies remains if one also wants to
package `diskExtraS` as a full `ExtraDegeneracy`; Section 4 does not need it.
-/

/-- The sole remaining identity needed to turn `diskExtraS` into a full extra
degeneracy.  No inhabitant is asserted because this optional strengthening is
not needed for reduced integral acyclicity. -/
structure RemainingNaturalityData (G : AddCommGrpCat.{u}) (q : ℕ) : Prop where
  s_comp_sigma :
    ∀ (n : ℕ) (i : Fin (n + 1)),
      diskExtraS G q n ≫
          (Γ₀.obj (diskSuccComplex G q)).σ i.succ =
        (Γ₀.obj (diskSuccComplex G q)).σ i ≫ diskExtraS G q (n + 1)

/-- Once the explicitly displayed remaining naturality identities are
proved, the summand formula gives an actual extra degeneracy of the standard
Dold--Kan disk model. -/
def diskExtraDegeneracy (G : AddCommGrpCat.{u}) (q : ℕ)
    (H : RemainingNaturalityData G q) :
    LExtraDegeneracy G q where
  s' := 0
  s n := diskExtraS G q n
  s'_comp_ε := by
    exact (isZero_zero AddCommGrpCat).eq_of_tgt _ _
  s₀_comp_δ₁ := by
    rw [comp_zero]
    exact diskExtraS_zero_comp_δ_one G q
  s_comp_δ₀ n := by
    exact diskExtraS_comp_δ_zero G q n
  s_comp_δ n i := diskExtraS_comp_δ_succ G q n i
  s_comp_σ n i := H.s_comp_sigma n i

/-- The same conditional construction in the minimal form needed by reduced
linearization: a simplicial contraction from zero to the identity. -/
def diskSimplicialContraction (G : AddCommGrpCat.{u}) (q : ℕ)
    (H : RemainingNaturalityData G q) :
    LSimplicialContraction G q :=
  simplicialContractionOfExtraDegeneracy (diskExtraDegeneracy G q H)

/-- Thus the remaining coordinate identities are sufficient for the exact
reduced integral acyclicity statement used in Section 4. -/
theorem reducedFreeL_acyclic_of_remainingNaturalityData
    (G : AddCommGrpCat.{u}) (q : ℕ)
    (H : RemainingNaturalityData G q) :
    (AlgebraicTopology.AlternatingFaceMapComplex.obj
      (reducedFree (L G (q + 1)))).Acyclic :=
  reducedFreeL_alternating_acyclic G q (diskExtraDegeneracy G q H)

end DoldKanDiskContraction

end GeneralSphereT.StandardModels
