import Formalization.Section4LiteralConeHomotopyDescent

set_option linter.style.header false

/-!
# Extra-degeneracy contractions and the literal cone quotient

The literal `Option` cone identifies cylinder simplices with the same cut
and the same suffix after that cut.  This file proves the matching structural
fact for the cylinder homotopy supplied by an extra degeneracy: away from the
all-zero cut, its cut component factors through the iterated zeroth face that
forgets exactly that initial prefix.
-/

noncomputable section

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits ZeroObject
  Opposite Simplicial
open SimplicialObject.Augmented
open MonoidalCategory CartesianMonoidalCategory
open CategoryTheory.Limits
open Limits

open GeneralSphereT.SimplicialCochain
open GeneralSphereT.Section4.UnderlyingSSet
open GeneralSphereT.Section4.RelativeMapping
open GeneralSphereT.Section4.NativeRelativeHomotopyGroup
open GeneralSphereT.Section4.SimplicialObjectCylinderHomotopy

namespace GeneralSphereT.Section4.ExtraDegeneracyLiteralDescent

universe u

variable {C : Type u} [Category C]
variable {X : SimplicialObject.Augmented C}

/-- At every nonterminal cut, the prism contraction associated to an extra
degeneracy factors through the suffix obtained by deleting the initial
vertices before the cut. -/
theorem homotopy_h_comp_delta_succ_factor
    (ed : ExtraDegeneracy X) (a b : ℕ) :
    ed.homotopy.h
          (⟨a, by omega⟩ : Fin (a + b + 1 + 1)) ≫
        X.left.δ (⟨a, by omega⟩ : Fin (a + b + 1 + 1)).succ =
      X.left.δ₀Iter (a + 1) (n := b) (by omega) ≫
        ed.s b ≫ X.left.σ₀Iter a (by omega) := by
  let i : Fin (a + b + 1 + 1) := ⟨a, by omega⟩
  change ExtraDegeneracy.homotopy.h ed i ≫ X.left.δ i.succ = _
  rw [ExtraDegeneracy.homotopy.h_eq_assoc ed i (b + 1) (by
    dsimp [i]
    omega)]
  slice_lhs 3 4 =>
    rw [X.left.σ₀Iter_δ' i.succ a
      (i' := (0 : Fin (b + 2)).succ)
      (m := b + 1) (by omega) (by grind) (by
        simp [i, Nat.add_comm])]
  slice_lhs 2 3 =>
    rw [ed.s_comp_δ b (0 : Fin (b + 2))]
  dsimp [i]
  simp only [← Category.assoc]
  rw [← X.left.δ₀Iter_succ' a (by omega)]

/-- Forming the prism homotopy from an extra degeneracy commutes, on its
prism operators, with applying a functor. -/
theorem map_homotopy_h
    {D : Type u} [Category D]
    (ed : ExtraDegeneracy X) (F : C ⥤ D)
    {n : ℕ} (i : Fin (n + 1)) :
    ((ed.map F).homotopy.h i) = F.map (ed.homotopy.h i) := by
  dsimp [ExtraDegeneracy.homotopy, ExtraDegeneracy.homotopy.h,
    ExtraDegeneracy.map, SimplicialObject.δ₀Iter,
    SimplicialObject.σ₀Iter]
  simp only [Functor.map_comp]
  rfl

/-! ## Fibers of the literal cone quotient -/

universe v

variable {V : Type v} [LinearOrder V] [Fintype V]
variable (M : AbstractSimplicialComplex V)

local instance (priority := 10000) extraDescentOptionLE : LE (Option V) :=
  @WithBot.instLE V inferInstance

local instance (priority := 10000) extraDescentOptionLT : LT (Option V) :=
  @WithBot.instLT V inferInstance

local instance (priority := 10000) extraDescentOptionLinearOrder :
    LinearOrder (Option V) :=
  @WithBot.linearOrder V inferInstance

/-- The literal quotient remembers the cut of an interval simplex. -/
theorem literalConeCylinderQuotient_objMk₁_cut_injective
    {n : ℕ}
    (x y : (orderedComplexSSet M).obj (op (SimplexCategory.mk n)))
    (k l : Fin (n + 2))
    (h : (literalConeCylinderQuotient M).app (op (SimplexCategory.mk n))
          (x, SSet.stdSimplex.objMk₁.{v} k) =
        (literalConeCylinderQuotient M).app (op (SimplexCategory.mk n))
          (y, SSet.stdSimplex.objMk₁.{v} l)) :
    k = l := by
  apply le_antisymm
  · by_contra hnot
    have hlk : l < k := lt_of_not_ge hnot
    let j : Fin (n + 1) := ⟨l.val, by omega⟩
    have hjl : ¬ j.castSucc < l := by
      simp [j]
    have hjk : j.castSucc < k := by
      simpa [j] using hlk
    have hv := congrArg (fun z ↦ z.1 j) h
    change
      (if SSet.stdSimplex.objMk₁.{v} k j = 0 then none else some (x.1 j)) =
        (if SSet.stdSimplex.objMk₁.{v} l j = 0 then none else some (y.1 j)) at hv
    have htk : SSet.stdSimplex.objMk₁.{v} k j = 0 :=
      SSet.stdSimplex.objMk₁_of_castSucc_lt.{v} k j hjk
    have htl : SSet.stdSimplex.objMk₁.{v} l j = 1 :=
      SSet.stdSimplex.objMk₁_of_le_castSucc.{v} l j (by omega)
    have htl0 : SSet.stdSimplex.objMk₁.{v} l j ≠ 0 := by
      rw [htl]
      decide
    rw [if_pos htk, if_neg htl0] at hv
    cases hv
  · by_contra hnot
    have hkl : k < l := lt_of_not_ge hnot
    let j : Fin (n + 1) := ⟨k.val, by omega⟩
    have hjk : ¬ j.castSucc < k := by
      simp [j]
    have hjl : j.castSucc < l := by
      simpa [j] using hkl
    have hv := congrArg (fun z ↦ z.1 j) h
    change
      (if SSet.stdSimplex.objMk₁.{v} k j = 0 then none else some (x.1 j)) =
        (if SSet.stdSimplex.objMk₁.{v} l j = 0 then none else some (y.1 j)) at hv
    have htk : SSet.stdSimplex.objMk₁.{v} k j = 1 :=
      SSet.stdSimplex.objMk₁_of_le_castSucc.{v} k j (by omega)
    have htl : SSet.stdSimplex.objMk₁.{v} l j = 0 :=
      SSet.stdSimplex.objMk₁_of_castSucc_lt.{v} l j hjl
    have htk0 : SSet.stdSimplex.objMk₁.{v} k j ≠ 0 := by
      rw [htk]
      decide
    rw [if_neg htk0, if_pos htl] at hv
    cases hv

/-- In a fixed cut, equality in the literal quotient gives equality of all
bottom vertices at and after the cut. -/
theorem literalConeCylinderQuotient_objMk₁_suffix
    {n : ℕ}
    (x y : (orderedComplexSSet M).obj (op (SimplexCategory.mk n)))
    (k : Fin (n + 2))
    (h : (literalConeCylinderQuotient M).app (op (SimplexCategory.mk n))
          (x, SSet.stdSimplex.objMk₁.{v} k) =
        (literalConeCylinderQuotient M).app (op (SimplexCategory.mk n))
          (y, SSet.stdSimplex.objMk₁.{v} k))
    (j : Fin (n + 1)) (hkj : k ≤ j.castSucc) :
    x.1 j = y.1 j := by
  have hv := congrArg (fun z ↦ z.1 j) h
  change
    (if SSet.stdSimplex.objMk₁.{v} k j = 0 then none else some (x.1 j)) =
      (if SSet.stdSimplex.objMk₁.{v} k j = 0 then none else some (y.1 j)) at hv
  have ht0 : SSet.stdSimplex.objMk₁.{v} k j ≠ 0 := by
    intro ht
    have := (SSet.stdSimplex.objMk₁_apply_eq_zero_iff.{v} k j).mp ht
    exact (not_lt_of_ge hkj) this
  rw [if_neg ht0, if_neg ht0] at hv
  exact Option.some.inj hv

/-- For a nonterminal cut `a + 1`, equality in the quotient is exactly the
amount of equality needed by the iterated zeroth face in the factorization
of the extra-degeneracy prism. -/
theorem literalConeCylinderQuotient_objMk₁_delta₀Iter_eq
    (a b : ℕ)
    (x y : (orderedComplexSSet M).obj
      (op (SimplexCategory.mk (a + b + 1))))
    (h : (literalConeCylinderQuotient M).app
          (op (SimplexCategory.mk (a + b + 1)))
          (x, SSet.stdSimplex.objMk₁.{v}
            (⟨a + 1, by omega⟩ : Fin (a + b + 1 + 2))) =
        (literalConeCylinderQuotient M).app
          (op (SimplexCategory.mk (a + b + 1)))
          (y, SSet.stdSimplex.objMk₁.{v}
            (⟨a + 1, by omega⟩ : Fin (a + b + 1 + 2)))) :
    ((orderedComplexSSet M).δ₀Iter (a + 1) (n := b) (by omega)).hom x =
      ((orderedComplexSSet M).δ₀Iter (a + 1) (n := b) (by omega)).hom y := by
  change
    (orderedComplexSSet M).map
        (SimplexCategory.δ₀Iter (a + 1) (n := b) (by omega)).op x =
      (orderedComplexSSet M).map
        (SimplexCategory.δ₀Iter (a + 1) (n := b) (by omega)).op y
  apply Subtype.ext
  simp only [orderedComplexSSet_map_coe]
  apply OrderHom.ext
  funext j
  have hj : j.val < b + 1 := by
    simpa only [SimplexCategory.len_mk] using j.isLt
  let r : Fin (a + b + 1 + 1) := ⟨j.val + (a + 1), by omega⟩
  have hr := literalConeCylinderQuotient_objMk₁_suffix M x y
    (⟨a + 1, by omega⟩ : Fin (a + b + 1 + 2)) h
    r (by
      change a + 1 ≤ r.val
      dsimp [r]
      omega)
  change x.1 ((SimplexCategory.δ₀Iter (a + 1)
    (n := b) (by omega)).toOrderHom j) =
      y.1 ((SimplexCategory.δ₀Iter (a + 1)
        (n := b) (by omega)).toOrderHom j)
  have heq : (SimplexCategory.δ₀Iter (a + 1)
      (n := b) (by omega)).toOrderHom j = r := by
    apply Fin.ext
    rfl
  rw [heq]
  exact hr

/-! ## Pointwise descent for an extra degeneracy -/

variable {T : SimplicialObject.Augmented (Type v)}

/-- At a nonterminal cut, the cylinder value of the extra-degeneracy
homotopy only depends on the suffix selected by `δ₀Iter`. -/
theorem extraDegeneracy_cylinderApp_objMk₁_eq_of_delta₀Iter_eq
    (ed : ExtraDegeneracy T) (a b : ℕ)
    (x y : T.left.obj (op (SimplexCategory.mk (a + b + 1))))
    (hxy : (T.left.δ₀Iter (a + 1) (n := b) (by omega)).hom x =
      (T.left.δ₀Iter (a + 1) (n := b) (by omega)).hom y) :
    (cylinderApp ed.homotopy (a + b + 1)).hom
        (x, SSet.stdSimplex.objMk₁.{v}
          (⟨a + 1, by omega⟩ : Fin (a + b + 1 + 2))) =
      (cylinderApp ed.homotopy (a + b + 1)).hom
        (y, SSet.stdSimplex.objMk₁.{v}
          (⟨a + 1, by omega⟩ : Fin (a + b + 1 + 2))) := by
  rw [cylinderApp_apply_objMk₁, cylinderApp_apply_objMk₁]
  simp only [show
    (⟨a + 1, by omega⟩ : Fin (a + b + 1 + 2)) =
      (⟨a, by omega⟩ : Fin (a + b + 1 + 1)).succ by rfl,
    prismIndex_succ]
  rw [homotopy_h_comp_delta_succ_factor ed a b]
  change
    ((ed.s b ≫ T.left.σ₀Iter a (by omega)).hom
      ((T.left.δ₀Iter (a + 1) (n := b) (by omega)).hom x)) =
      ((ed.s b ≫ T.left.σ₀Iter a (by omega)).hom
        ((T.left.δ₀Iter (a + 1) (n := b) (by omega)).hom y))
  rw [hxy]

/-- A precomposed extra-degeneracy cylinder map is constant on the fibers
of the literal cone quotient as soon as its all-zero cut is constant.  The
latter is automatic for a contraction whose zero endpoint is a constant
map (in particular, for the zero contraction of a simplicial abelian
group). -/
theorem extraDegeneracy_precomp_cylinderMap_fiberInvariant
    (ed : ExtraDegeneracy T)
    (f : orderedComplexSSet M ⟶ T.left)
    (hterminal : ∀ (n : ℕ)
        (x y : (orderedComplexSSet M).obj
          (op (SimplexCategory.mk n))),
      (cylinderApp ed.homotopy n).hom
          (f.app (op (SimplexCategory.mk n)) x,
            SSet.stdSimplex.objMk₁.{v} (Fin.last (n + 1))) =
        (cylinderApp ed.homotopy n).hom
          (f.app (op (SimplexCategory.mk n)) y,
            SSet.stdSimplex.objMk₁.{v} (Fin.last (n + 1)))) :
    LiteralConeFiberInvariant M
      (f ▷ Δ[1] ≫ cylinderMap ed.homotopy) := by
  intro Delta z w hq
  induction Delta using Opposite.rec with
  | _ Delta =>
    induction Delta using SimplexCategory.rec with
    | _ n =>
      rcases z with ⟨x, t⟩
      rcases w with ⟨y, u⟩
      obtain ⟨k, rfl⟩ := SSet.stdSimplex.objMk₁_surjective t
      obtain ⟨l, rfl⟩ := SSet.stdSimplex.objMk₁_surjective u
      have hkl : k = l :=
        literalConeCylinderQuotient_objMk₁_cut_injective M x y k l hq
      subst l
      change
        (cylinderApp ed.homotopy n).hom
            (f.app (op (SimplexCategory.mk n)) x,
              SSet.stdSimplex.objMk₁ k) =
          (cylinderApp ed.homotopy n).hom
            (f.app (op (SimplexCategory.mk n)) y,
              SSet.stdSimplex.objMk₁ k)
      rcases Fin.eq_zero_or_eq_succ k with rfl | ⟨i, rfl⟩
      · have hxy : x = y := by
          apply Subtype.ext
          apply OrderHom.ext
          funext j
          exact literalConeCylinderQuotient_objMk₁_suffix M x y 0 hq j
            (Fin.zero_le _)
        subst y
        rfl
      · by_cases hi : i = Fin.last n
        · subst i
          exact hterminal n x y
        · obtain ⟨p, rfl⟩ := Fin.eq_castSucc_of_ne_last hi
          obtain ⟨a, ha⟩ := p
          obtain ⟨b, rfl⟩ : ∃ b, n = a + b + 1 :=
            ⟨n - a - 1, by omega⟩
          have hab : b + (a + 1) = a + b + 1 := by
            ac_rfl
          have hk :
              (⟨a, ha⟩ : Fin (a + b + 1)).castSucc.succ =
                (⟨a + 1, by omega⟩ : Fin (a + b + 1 + 2)) := by
            apply Fin.ext
            rfl
          rw [hk] at hq ⊢
          have hsource :=
            literalConeCylinderQuotient_objMk₁_delta₀Iter_eq
              M a b x y hq
          let theta :=
            (SimplexCategory.δ₀Iter (a + 1) (n := b) hab).op
          have htarget :
              (T.left.δ₀Iter (a + 1) (n := b) hab).hom
                    (f.app (op (SimplexCategory.mk (a + b + 1))) x) =
                (T.left.δ₀Iter (a + 1) (n := b) hab).hom
                    (f.app (op (SimplexCategory.mk (a + b + 1))) y) := by
            calc
              _ = f.app (op (SimplexCategory.mk b))
                    ((orderedComplexSSet M).δ₀Iter
                      (a + 1) (n := b) hab x) := by
                exact (f.naturality_apply theta x).symm
              _ = f.app (op (SimplexCategory.mk b))
                    ((orderedComplexSSet M).δ₀Iter
                      (a + 1) (n := b) hab y) := by
                rw [hsource]
              _ = _ := f.naturality_apply theta y
          exact extraDegeneracy_cylinderApp_objMk₁_eq_of_delta₀Iter_eq
            ed a b _ _ htarget

/-- The all-zero cut of an extra-degeneracy cylinder is constant when the
augmentation object is a subsingleton. -/
theorem extraDegeneracy_cylinderApp_last_eq
    [Subsingleton T.right]
    (ed : ExtraDegeneracy T) (n : ℕ)
    (x y : T.left.obj (op (SimplexCategory.mk n))) :
    (cylinderApp ed.homotopy n).hom
        (x, SSet.stdSimplex.objMk₁.{v} (Fin.last (n + 1))) =
      (cylinderApp ed.homotopy n).hom
        (y, SSet.stdSimplex.objMk₁.{v} (Fin.last (n + 1))) := by
  rw [cylinderApp_apply_objMk₁, cylinderApp_apply_objMk₁]
  have hk : (Fin.last (n + 1) : Fin (n + 2)) =
      (Fin.last n : Fin (n + 1)).succ := by
    apply Fin.ext
    simp
  rw [hk, prismIndex_succ]
  have hk' : (Fin.last n : Fin (n + 1)).succ =
      (Fin.last (n + 1) : Fin (n + 2)) := hk.symm
  rw [hk', ed.homotopy.h_last_comp_δ_last]
  change
    (ed.section_.app (op (SimplexCategory.mk n))).hom
        ((T.hom.app (op (SimplexCategory.mk n))).hom x) =
      (ed.section_.app (op (SimplexCategory.mk n))).hom
        ((T.hom.app (op (SimplexCategory.mk n))).hom y)
  have haug :
      (T.hom.app (op (SimplexCategory.mk n))).hom x =
        (T.hom.app (op (SimplexCategory.mk n))).hom y := by
    change (_ : T.right) = _
    exact Subsingleton.elim _ _
  rw [haug]

/-- Convenient form of the fiber-invariance theorem for an augmented
simplicial set with a subsingleton augmentation object. -/
theorem extraDegeneracy_precomp_cylinderMap_fiberInvariant_of_subsingleton
    [Subsingleton T.right]
    (ed : ExtraDegeneracy T)
    (f : orderedComplexSSet M ⟶ T.left) :
    LiteralConeFiberInvariant M
      (f ▷ Δ[1] ≫ cylinderMap ed.homotopy) :=
  extraDegeneracy_precomp_cylinderMap_fiberInvariant M ed f
    (fun n x y ↦ extraDegeneracy_cylinderApp_last_eq ed n _ _)

/-! ## The reduced-free standard disk -/

open GeneralSphereT.StandardModels
open GeneralSphereT.StandardModels.DoldKanDiskContraction
open GeneralSphereT.PathAlgebra

/-- The standard disk extra degeneracy, first sent through reduced
linearization and then forgotten to sets.  Its left simplicial object is
definitionally the underlying simplicial set of `reducedFree (L G (q+1))`.
-/
abbrev standardDiskReducedFreeUnderlyingAugmented
    (G : AddCommGrpCat.{v}) (q : ℕ) :
    SimplicialObject.Augmented (Type v) :=
  ((SimplicialObject.Augmented.whiskering AddCommGrpCat (Type v)).obj
    (forget AddCommGrpCat)).obj
      (((SimplicialObject.Augmented.whiskering AddCommGrpCat
        AddCommGrpCat).obj reducedFreeBaseFunctor).obj
          (zeroAugmentation (L G (q + 1))))

def standardDiskReducedFreeUnderlyingExtraDegeneracy
    (G : AddCommGrpCat.{v}) (q : ℕ) :
    ExtraDegeneracy (standardDiskReducedFreeUnderlyingAugmented G q) :=
  (reducedFreeExtraDegeneracy (standardDiskExtraDegeneracy G q)).map
    (forget AddCommGrpCat)

/-- The augmentation object of the reduced-free standard disk is the
reduced free group on the zero group, hence has one underlying element. -/
theorem standardDiskReducedFreeUnderlyingRightSubsingleton
    (G : AddCommGrpCat.{v}) (q : ℕ) :
    Subsingleton
      (standardDiskReducedFreeUnderlyingAugmented G q).right := by
  change Subsingleton
    (reducedFreeBaseFunctor.obj (0 : AddCommGrpCat.{v}))
  exact AddCommGrpCat.subsingleton_of_isZero
    reducedFreeBaseFunctor_zero_isZero

/-- The standard reduced-free disk cylinder is constant on literal-cone
quotient fibers.  This is the target-specific combinatorial heart of the
reverse cone criterion. -/
theorem standardDiskReducedFreeUnderlying_fiberInvariant
    (G : AddCommGrpCat.{v}) (q : ℕ)
    (f : orderedComplexSSet M ⟶
      GeneralSphereT.Section4.underlyingSSet
        (reducedFree (L G (q + 1)))) :
    LiteralConeFiberInvariant M
      (f ▷ Δ[1] ≫
        cylinderMap
          (standardDiskReducedFreeUnderlyingExtraDegeneracy G q).homotopy) := by
  letI := standardDiskReducedFreeUnderlyingRightSubsingleton G q
  exact extraDegeneracy_precomp_cylinderMap_fiberInvariant_of_subsingleton
    M (standardDiskReducedFreeUnderlyingExtraDegeneracy G q) f

/-- The zero element, named at the underlying augmented-object type.  This
small wrapper avoids asking type-class inference to recover the additive
structure after both functors have been forgotten to `Type`. -/
def standardDiskReducedFreeUnderlyingZero
    (G : AddCommGrpCat.{v}) (q n : ℕ) :
    (standardDiskReducedFreeUnderlyingAugmented G q).left.obj
      (op (SimplexCategory.mk n)) := by
  change RedDist ((L G (q + 1)).obj (op (SimplexCategory.mk n)))
  exact 0

/-- Every prism operator of the mapped extra degeneracy preserves the zero
element. -/
theorem standardDiskReducedFreeUnderlying_cylinderApp_zero
    (G : AddCommGrpCat.{v}) (q n : ℕ)
    (t : Δ[1].obj (op (SimplexCategory.mk n))) :
    (cylinderApp
      (standardDiskReducedFreeUnderlyingExtraDegeneracy G q).homotopy n).hom
        (standardDiskReducedFreeUnderlyingZero G q n, t) =
      standardDiskReducedFreeUnderlyingZero G q n := by
  obtain ⟨k, rfl⟩ := SSet.stdSimplex.objMk₁_surjective t
  rw [cylinderApp_apply_objMk₁]
  unfold standardDiskReducedFreeUnderlyingExtraDegeneracy
  rw [map_homotopy_h
    (reducedFreeExtraDegeneracy (standardDiskExtraDegeneracy G q))
    (forget AddCommGrpCat) (prismIndex k)]
  change _ = (0 : RedDist
    ((L G (q + 1)).obj (op (SimplexCategory.mk n))))
  rfl

/-- The all-zero endpoint of the mapped extra-degeneracy cylinder is the
zero map. -/
theorem standardDiskReducedFreeUnderlying_cylinder_h₀
    (G : AddCommGrpCat.{v}) (q : ℕ) :
    SSet.ι₀ ≫ cylinderMap
      (standardDiskReducedFreeUnderlyingExtraDegeneracy G q).homotopy =
      (0 : GeneralSphereT.Section4.underlyingSSet
        (reducedFree (L G (q + 1))) ⟶
        GeneralSphereT.Section4.underlyingSSet
          (reducedFree (L G (q + 1)))) := by
  letI := standardDiskReducedFreeUnderlyingRightSubsingleton G q
  ext Delta x
  induction Delta using Opposite.rec with
  | _ Delta =>
    induction Delta using SimplexCategory.rec with
    | _ n =>
      change (cylinderApp
        (standardDiskReducedFreeUnderlyingExtraDegeneracy G q).homotopy n).hom
          (SSet.ι₀.app (op (SimplexCategory.mk n)) x) =
        standardDiskReducedFreeUnderlyingZero G q n
      rw [ι₀_app_eq_objMk₁_last]
      calc
        _ = (cylinderApp
            (standardDiskReducedFreeUnderlyingExtraDegeneracy G q).homotopy n).hom
              (standardDiskReducedFreeUnderlyingZero G q n,
                SSet.stdSimplex.objMk₁ (Fin.last (n + 1))) :=
          extraDegeneracy_cylinderApp_last_eq
            (standardDiskReducedFreeUnderlyingExtraDegeneracy G q) n _ _
        _ = standardDiskReducedFreeUnderlyingZero G q n :=
          standardDiskReducedFreeUnderlying_cylinderApp_zero G q n _

/-- The all-one endpoint of the mapped extra-degeneracy cylinder is the
identity. -/
theorem standardDiskReducedFreeUnderlying_cylinder_h₁
    (G : AddCommGrpCat.{v}) (q : ℕ) :
    SSet.ι₁ ≫ cylinderMap
      (standardDiskReducedFreeUnderlyingExtraDegeneracy G q).homotopy =
      𝟙 (GeneralSphereT.Section4.underlyingSSet
        (reducedFree (L G (q + 1)))) := by
  ext Delta x
  induction Delta using Opposite.rec with
  | _ Delta =>
    induction Delta using SimplexCategory.rec with
    | _ n =>
      change (cylinderApp
        (standardDiskReducedFreeUnderlyingExtraDegeneracy G q).homotopy n).hom
          (SSet.ι₁.app (op (SimplexCategory.mk n)) x) = x
      rw [ι₁_app_eq_objMk₁_zero, cylinderApp_apply_objMk₁]
      change
        (((standardDiskReducedFreeUnderlyingExtraDegeneracy G q).homotopy.h 0 ≫
          (standardDiskReducedFreeUnderlyingAugmented G q).left.δ 0).hom x) = x
      rw [(standardDiskReducedFreeUnderlyingExtraDegeneracy G q).homotopy.h_zero_comp_δ_zero]
      rfl

/-- The mapped extra-degeneracy cylinder preserves the distinguished zero
vertex throughout the interval. -/
theorem standardDiskReducedFreeUnderlying_zeroCylinder
    (G : AddCommGrpCat.{v}) (q : ℕ) :
    ((zeroSubcomplex (reducedFree (L G (q + 1)))).ι ▷ Δ[1]) ≫
        cylinderMap
          (standardDiskReducedFreeUnderlyingExtraDegeneracy G q).homotopy =
      (0 : (zeroSubcomplex (reducedFree (L G (q + 1))) : SSet) ⊗ Δ[1] ⟶
        underlyingSSet (reducedFree (L G (q + 1)))) := by
  ext Delta z
  induction Delta using Opposite.rec with
  | _ Delta =>
    induction Delta using SimplexCategory.rec with
    | _ n =>
      change (cylinderApp
        (standardDiskReducedFreeUnderlyingExtraDegeneracy G q).homotopy n).hom
          (((zeroSubcomplex (reducedFree (L G (q + 1)))).ι.app
            (op (SimplexCategory.mk n))) z.1, z.2) =
        standardDiskReducedFreeUnderlyingZero G q n
      have hzero :
          (zeroSubcomplex (reducedFree (L G (q + 1)))).ι =
            (0 : (zeroSubcomplex (reducedFree (L G (q + 1))) : SSet) ⟶
              underlyingSSet (reducedFree (L G (q + 1)))) := by
        rw [SSet.Subcomplex.ofSimplex_ι, const_zeroVertex_eq_zeroMap]
      have hz :
          ((zeroSubcomplex (reducedFree (L G (q + 1)))).ι.app
            (op (SimplexCategory.mk n))) z.1 =
            standardDiskReducedFreeUnderlyingZero G q n := by
        rw [hzero]
        change _ = (0 : RedDist
          ((L G (q + 1)).obj (op (SimplexCategory.mk n))))
        rfl
      rw [hz]
      exact standardDiskReducedFreeUnderlying_cylinderApp_zero G q n z.2

/-! ## Unconditional literal extension for the standard disk -/

/-- The contraction obtained directly from the mapped extra degeneracy,
relative to an arbitrary source subcomplex.  Its cylinder is the one for
which fiber invariance was proved above. -/
def standardDiskReducedFreeExtraDegeneracyRelativeContraction
    (P : (orderedComplexSSet M).Subcomplex)
    (G : AddCommGrpCat.{v}) (q : ℕ)
    (f : NativeRelativeMorphism P (reducedFree (L G (q + 1)))) :
    SSet.RelativeMorphism.Homotopy
      (0 : NativeRelativeMorphism P (reducedFree (L G (q + 1)))) f where
  h := f.map ▷ Δ[1] ≫ cylinderMap
    (standardDiskReducedFreeUnderlyingExtraDegeneracy G q).homotopy
  h₀ := by
    rw [SSet.ι₀_comp_assoc]
    have hcomp := congrArg (fun k ↦ f.map ≫ k)
      (standardDiskReducedFreeUnderlying_cylinder_h₀ G q)
    have hzero :
        f.map ≫ (0 : underlyingSSet (reducedFree (L G (q + 1))) ⟶
          underlyingSSet (reducedFree (L G (q + 1)))) =
          (0 : NativeRelativeMorphism P
            (reducedFree (L G (q + 1)))).map := by
      calc
        _ = (0 : orderedComplexSSet M ⟶
            underlyingSSet (reducedFree (L G (q + 1)))) := by
          ext Delta x
          rfl
        _ = (0 : NativeRelativeMorphism P
            (reducedFree (L G (q + 1)))).map :=
          (relativeMorphism_zero_map P _).symm
    exact hcomp.trans hzero
  h₁ := by
    rw [SSet.ι₁_comp_assoc]
    have hcomp := congrArg (fun k ↦ f.map ≫ k)
      (standardDiskReducedFreeUnderlying_cylinder_h₁ G q)
    exact hcomp.trans (Category.comp_id f.map)
  rel := by
    rw [← comp_whiskerRight_assoc, f.comm, comp_whiskerRight_assoc]
    have hpre := congrArg
      (fun k ↦ zeroBoundary P (reducedFree (L G (q + 1))) ▷ Δ[1] ≫ k)
      (standardDiskReducedFreeUnderlying_zeroCylinder G q)
    have hzero :
        zeroBoundary P (reducedFree (L G (q + 1))) ▷ Δ[1] ≫
            (0 : (zeroSubcomplex (reducedFree (L G (q + 1))) : SSet) ⊗ Δ[1] ⟶
              underlyingSSet (reducedFree (L G (q + 1)))) =
          (0 : (P : SSet) ⊗ Δ[1] ⟶
            underlyingSSet (reducedFree (L G (q + 1)))) := by
      ext Delta x
      rfl
    exact hpre.trans (hzero.trans (cylinder_zeroBoundary P _).symm)

/-- The explicit extra-degeneracy contraction descends through the literal
`Option`-cone quotient.  No Kan hypothesis or comparison with a categorical
cone is needed. -/
def standardDiskReducedFreeExtraDegeneracyLiteralDescent
    (P : (orderedComplexSSet M).Subcomplex) (b : V)
    (G : AddCommGrpCat.{v}) (q : ℕ)
    (f : NativeRelativeMorphism P (reducedFree (L G (q + 1)))) :
    LiteralRelativeHomotopyDescent M P (reducedFree (L G (q + 1)))
      (standardDiskReducedFreeExtraDegeneracyRelativeContraction M P G q f) := by
  let H := standardDiskReducedFreeExtraDegeneracyRelativeContraction M P G q f
  let hinv := standardDiskReducedFreeUnderlying_fiberInvariant M G q f.map
  let descended := literalConeDescendedMap M b H.h hinv
  refine
    { map := descended
      quotient := literalConeCylinderQuotient_descendedMap M b H.h hinv
      apex := ?_ }
  calc
    SSet.const (literalConeApex M) ≫ descended =
        (SSet.ι₀ ≫ literalConeCylinderQuotient M) ≫ descended := by
      rw [ι₀_literalConeCylinderQuotient]
    _ = SSet.ι₀ ≫ (literalConeCylinderQuotient M ≫ descended) :=
      Category.assoc _ _ _
    _ = SSet.ι₀ ≫ H.h := by
      exact congrArg (fun k ↦ SSet.ι₀ ≫ k)
        (literalConeCylinderQuotient_descendedMap M b H.h hinv)
    _ = (0 : NativeRelativeMorphism P
        (reducedFree (L G (q + 1)))).map := H.h₀
    _ = (0 : orderedComplexSSet M ⟶
        underlyingSSet (reducedFree (L G (q + 1)))) :=
      relativeMorphism_zero_map P _

/-- Every strictly relative map into the reduced-free Dold--Kan standard
disk extends over the literal simplicial cone, while remaining zero on the
cone over the source subcomplex.  This is the literal-cone form of (4.21). -/
def standardDiskReducedFreeExtraDegeneracyLiteralExtension
    (P : (orderedComplexSSet M).Subcomplex) (b : V)
    (G : AddCommGrpCat.{v}) (q : ℕ)
    (f : NativeRelativeMorphism P (reducedFree (L G (q + 1)))) :
    LiteralRelativeExtension M P (reducedFree (L G (q + 1))) f :=
  (standardDiskReducedFreeExtraDegeneracyLiteralDescent M P b G q f).toLiteralRelativeExtension

end GeneralSphereT.Section4.ExtraDegeneracyLiteralDescent
