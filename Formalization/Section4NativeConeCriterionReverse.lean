import Formalization.Section4LiteralConeBoundaryHEP
import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.PushoutProduct

set_option linter.style.header false

/-!
# Section 4: lifting a native nullhomotopy to the pointed literal cone

This file develops the homotopy-extension route for the reverse implication
in the native pointed cone criterion.  The first ingredient is a small,
general path-lifting lemma for Kan fibrations.  It is stated directly in
terms of maps from the standard 0- and 1-simplices, so it can be applied to
restriction maps between internal mapping objects.
-/

noncomputable section

open CategoryTheory CategoryTheory.Category Opposite Simplicial SSet
open MonoidalCategory CartesianMonoidalCategory MonoidalClosed
open HomotopicalAlgebra
open scoped SSet.modelCategoryQuillen

namespace GeneralSphereT.Section4.NativeConeCriterionReverse

universe u

variable {E B : SSet.{u}}

private def pathLiftFaces (e₀ : Δ[0] ⟶ E) :
    ∀ (j : Fin 2) (_ : j ≠ (0 : Fin 2)), Δ[0] ⟶ E :=
  fun _ _ ↦ e₀

private theorem pathLiftFaces_compatible (e₀ : Δ[0] ⟶ E) :
    horn.IsCompatible (pathLiftFaces e₀) := by
  simp

private theorem pathLiftFaces_comm
    (p : E ⟶ B) (e₀ : Δ[0] ⟶ E) (path : Δ[1] ⟶ B)
    (h₀ : e₀ ≫ p = stdSimplex.δ (1 : Fin 2) ≫ path) :
    ∀ (j : Fin 2) (hj : j ≠ (0 : Fin 2)),
      pathLiftFaces e₀ j hj ≫ p = stdSimplex.δ j ≫ path := by
  intro j hj
  fin_cases j
  · exact (hj rfl).elim
  · exact h₀

/-- Lift an edge of the base of a Kan fibration from a prescribed point over
its initial vertex.  Here `stdSimplex.δ 1` selects vertex `0` of `Δ[1]`.

This is the one-dimensional horn lifting property, isolated because it is
exactly the operation needed to turn a path of boundary maps into a path of
extensions. -/
noncomputable def liftPathFrom
    (p : E ⟶ B) [Fibration p]
    (e₀ : Δ[0] ⟶ E) (path : Δ[1] ⟶ B)
    (h₀ : e₀ ≫ p = stdSimplex.δ (1 : Fin 2) ≫ path) :
    Δ[1] ⟶ E :=
  (pathLiftFaces_compatible e₀).lift p path
    (pathLiftFaces_comm p e₀ path h₀)

@[reassoc]
theorem liftPathFrom_initial
    (p : E ⟶ B) [Fibration p]
    (e₀ : Δ[0] ⟶ E) (path : Δ[1] ⟶ B)
    (h₀ : e₀ ≫ p = stdSimplex.δ (1 : Fin 2) ≫ path) :
    stdSimplex.δ (1 : Fin 2) ≫ liftPathFrom p e₀ path h₀ = e₀ := by
  simpa only [liftPathFrom, pathLiftFaces] using
    (pathLiftFaces_compatible e₀).δ_lift p path
      (pathLiftFaces_comm p e₀ path h₀) (1 : Fin 2) (by decide)

@[reassoc]
theorem liftPathFrom_projects
    (p : E ⟶ B) [Fibration p]
    (e₀ : Δ[0] ⟶ E) (path : Δ[1] ⟶ B)
    (h₀ : e₀ ≫ p = stdSimplex.δ (1 : Fin 2) ≫ path) :
    liftPathFrom p e₀ path h₀ ≫ p = path := by
  exact (pathLiftFaces_compatible e₀).lift_comp p path
    (pathLiftFaces_comm p e₀ path h₀)

/-- The terminal point of the lifted path. -/
noncomputable def liftPathFromTerminal
    (p : E ⟶ B) [Fibration p]
    (e₀ : Δ[0] ⟶ E) (path : Δ[1] ⟶ B)
    (h₀ : e₀ ≫ p = stdSimplex.δ (1 : Fin 2) ≫ path) :
    Δ[0] ⟶ E :=
  stdSimplex.δ (0 : Fin 2) ≫ liftPathFrom p e₀ path h₀

@[reassoc]
theorem liftPathFromTerminal_projects
    (p : E ⟶ B) [Fibration p]
    (e₀ : Δ[0] ⟶ E) (path : Δ[1] ⟶ B)
    (h₀ : e₀ ≫ p = stdSimplex.δ (1 : Fin 2) ≫ path) :
    liftPathFromTerminal p e₀ path h₀ ≫ p =
      stdSimplex.δ (0 : Fin 2) ≫ path := by
  rw [liftPathFromTerminal, Category.assoc, liftPathFrom_projects]

/-! ## Homotopy extension through an internal-Hom restriction fibration -/

variable {D X Y : SSet.{u}}

/-- The internal-Hom restriction map induced by `i : D ⟶ X`. -/
abbrev mappingRestriction (i : D ⟶ X) (Y : SSet.{u}) :
    (ihom X).obj Y ⟶ (ihom D).obj Y :=
  (MonoidalClosed.pre i).app Y

/-- Homotopy extension for a monomorphism, expressed before identifying
`X ⊗ Δ[0]` with `X`.

The datum `f₀` is the initial map, while `boundaryPath` is the prescribed
homotopy on `D`.  The compatibility equation says that their initial faces
agree.  If `Y` is Kan, path lifting for the internal-Hom restriction
fibration produces a homotopy on all of `X`. -/
noncomputable def extendHomotopy
    (i : D ⟶ X) [Mono i] (Y : SSet.{u}) [KanComplex Y]
    (f₀ : X ⊗ Δ[0] ⟶ Y) (boundaryPath : D ⊗ Δ[1] ⟶ Y)
    (initial : i ▷ Δ[0] ≫ f₀ =
      D ◁ stdSimplex.δ (1 : Fin 2) ≫ boundaryPath) :
    X ⊗ Δ[1] ⟶ Y := by
  let initialPoint : Δ[0] ⟶ (ihom X).obj Y := curry f₀
  let boundaryEdge : Δ[1] ⟶ (ihom D).obj Y := curry boundaryPath
  have initialPoint_projects :
      initialPoint ≫ mappingRestriction i Y =
        stdSimplex.δ (1 : Fin 2) ≫ boundaryEdge := by
    calc
      initialPoint ≫ mappingRestriction i Y =
          curry (i ▷ Δ[0] ≫ f₀) := by
        exact curry_pre_app i f₀
      _ = curry (D ◁ stdSimplex.δ (1 : Fin 2) ≫ boundaryPath) := by
        rw [initial]
      _ = stdSimplex.δ (1 : Fin 2) ≫ boundaryEdge := by
        exact curry_natural_left _ _
  exact uncurry
    (liftPathFrom (mappingRestriction i Y) initialPoint boundaryEdge
      initialPoint_projects)

@[reassoc]
theorem extendHomotopy_initial
    (i : D ⟶ X) [Mono i] (Y : SSet.{u}) [KanComplex Y]
    (f₀ : X ⊗ Δ[0] ⟶ Y) (boundaryPath : D ⊗ Δ[1] ⟶ Y)
    (initial : i ▷ Δ[0] ≫ f₀ =
      D ◁ stdSimplex.δ (1 : Fin 2) ≫ boundaryPath) :
    X ◁ stdSimplex.δ (1 : Fin 2) ≫
        extendHomotopy i Y f₀ boundaryPath initial = f₀ := by
  rw [extendHomotopy]
  rw [← uncurry_natural_left]
  rw [liftPathFrom_initial, uncurry_curry]

@[reassoc]
theorem extendHomotopy_restricts
    (i : D ⟶ X) [Mono i] (Y : SSet.{u}) [KanComplex Y]
    (f₀ : X ⊗ Δ[0] ⟶ Y) (boundaryPath : D ⊗ Δ[1] ⟶ Y)
    (initial : i ▷ Δ[0] ≫ f₀ =
      D ◁ stdSimplex.δ (1 : Fin 2) ≫ boundaryPath) :
    i ▷ Δ[1] ≫ extendHomotopy i Y f₀ boundaryPath initial =
      boundaryPath := by
  apply curry_injective
  rw [← curry_pre_app, extendHomotopy, curry_uncurry,
    liftPathFrom_projects]

/-- The terminal face of the extended homotopy. -/
noncomputable def extendedTerminalMap
    (i : D ⟶ X) [Mono i] (Y : SSet.{u}) [KanComplex Y]
    (f₀ : X ⊗ Δ[0] ⟶ Y) (boundaryPath : D ⊗ Δ[1] ⟶ Y)
    (initial : i ▷ Δ[0] ≫ f₀ =
      D ◁ stdSimplex.δ (1 : Fin 2) ≫ boundaryPath) :
    X ⊗ Δ[0] ⟶ Y :=
  X ◁ stdSimplex.δ (0 : Fin 2) ≫
    extendHomotopy i Y f₀ boundaryPath initial

@[reassoc]
theorem extendedTerminalMap_restricts
    (i : D ⟶ X) [Mono i] (Y : SSet.{u}) [KanComplex Y]
    (f₀ : X ⊗ Δ[0] ⟶ Y) (boundaryPath : D ⊗ Δ[1] ⟶ Y)
    (initial : i ▷ Δ[0] ≫ f₀ =
      D ◁ stdSimplex.δ (1 : Fin 2) ≫ boundaryPath) :
    i ▷ Δ[0] ≫ extendedTerminalMap i Y f₀ boundaryPath initial =
      D ◁ stdSimplex.δ (0 : Fin 2) ≫ boundaryPath := by
  rw [extendedTerminalMap]
  calc
    i ▷ Δ[0] ≫ X ◁ stdSimplex.δ (0 : Fin 2) ≫
          extendHomotopy i Y f₀ boundaryPath initial =
        (i ▷ Δ[0] ≫ X ◁ stdSimplex.δ (0 : Fin 2)) ≫
          extendHomotopy i Y f₀ boundaryPath initial :=
      (Category.assoc _ _ _).symm
    _ =
        (D ◁ stdSimplex.δ (0 : Fin 2) ≫ i ▷ Δ[1]) ≫
          extendHomotopy i Y f₀ boundaryPath initial := by
      rw [whisker_exchange]
    _ = D ◁ stdSimplex.δ (0 : Fin 2) ≫
          (i ▷ Δ[1] ≫
            extendHomotopy i Y f₀ boundaryPath initial) :=
      Category.assoc _ _ _
    _ = D ◁ stdSimplex.δ (0 : Fin 2) ≫ boundaryPath := by
      rw [extendHomotopy_restricts]

/-! ## Removing the inessential `Δ[0]` tensor factor -/

def deltaZeroProjection (X : SSet.{u}) : X ⊗ Δ[0] ⟶ X :=
  fst X Δ[0]

def deltaZeroSection (X : SSet.{u}) : X ⟶ X ⊗ Δ[0] :=
  lift (𝟙 X) (SSet.stdSimplex.isTerminalObj₀.from X)

@[reassoc, simp]
theorem deltaZeroSection_projection (X : SSet.{u}) :
    deltaZeroSection X ≫ deltaZeroProjection X = 𝟙 X := by
  exact lift_fst _ _

@[reassoc, simp]
theorem deltaZeroProjection_section (X : SSet.{u}) :
    deltaZeroProjection X ≫ deltaZeroSection X = 𝟙 (X ⊗ Δ[0]) := by
  apply CartesianMonoidalCategory.hom_ext
  · simp [deltaZeroProjection, deltaZeroSection]
  · apply SSet.stdSimplex.ext₀

/-- Regard an ordinary map as a map whose source has an inessential
`Delta[0]` factor. -/
def tensorDeltaZeroMap {X Y : SSet.{u}} (f : X ⟶ Y) : X ⊗ Δ[0] ⟶ Y :=
  deltaZeroProjection X ≫ f

/-- Remove an inessential `Delta[0]` factor from the source. -/
def untensorDeltaZeroMap {X Y : SSet.{u}} (f : X ⊗ Δ[0] ⟶ Y) : X ⟶ Y :=
  deltaZeroSection X ≫ f

@[simp]
theorem untensor_tensorDeltaZeroMap {X Y : SSet.{u}} (f : X ⟶ Y) :
    untensorDeltaZeroMap (tensorDeltaZeroMap f) = f := by
  rw [untensorDeltaZeroMap, tensorDeltaZeroMap, ← Category.assoc,
    deltaZeroSection_projection, Category.id_comp]

@[simp]
theorem tensor_untensorDeltaZeroMap {X Y : SSet.{u}}
    (f : X ⊗ Δ[0] ⟶ Y) :
    tensorDeltaZeroMap (untensorDeltaZeroMap f) = f := by
  rw [untensorDeltaZeroMap, tensorDeltaZeroMap, ← Category.assoc,
    deltaZeroProjection_section, Category.id_comp]

@[reassoc]
theorem whiskerRight_deltaZero_section (i : D ⟶ X) :
    deltaZeroSection D ≫ i ▷ Δ[0] = i ≫ deltaZeroSection X := by
  ext Δ x
  rfl

@[reassoc]
theorem whiskerRight_deltaZero_projection (i : D ⟶ X) :
    i ▷ Δ[0] ≫ deltaZeroProjection X = deltaZeroProjection D ≫ i := by
  ext Δ x
  rfl

@[reassoc]
theorem deltaZeroProjection_comp_ι₀ (X : SSet.{u}) :
    deltaZeroProjection X ≫ SSet.ι₀ =
      X ◁ SSet.stdSimplex.δ (1 : Fin 2) := by
  apply CartesianMonoidalCategory.hom_ext
  · ext Δ x
    rfl
  · rw [Category.assoc, SSet.ι₀_snd,
      CartesianMonoidalCategory.whiskerLeft_snd,
      SSet.stdSimplex.δ_one_eq_const]
    ext Δ x
    rfl

@[reassoc]
theorem deltaZeroProjection_comp_ι₁ (X : SSet.{u}) :
    deltaZeroProjection X ≫ SSet.ι₁ =
      X ◁ SSet.stdSimplex.δ (0 : Fin 2) := by
  apply CartesianMonoidalCategory.hom_ext
  · ext Δ x
    rfl
  · rw [Category.assoc, SSet.ι₁_snd,
      CartesianMonoidalCategory.whiskerLeft_snd,
      SSet.stdSimplex.δ_zero_eq_const]
    ext Δ x
    rfl

theorem tensorDeltaZeroMap_endpoint₀
    (h : X ⊗ Δ[1] ⟶ Y) :
    tensorDeltaZeroMap (SSet.ι₀ ≫ h) =
      X ◁ SSet.stdSimplex.δ (1 : Fin 2) ≫ h := by
  rw [tensorDeltaZeroMap, ← Category.assoc, deltaZeroProjection_comp_ι₀]

theorem tensorDeltaZeroMap_endpoint₁
    (h : X ⊗ Δ[1] ⟶ Y) :
    tensorDeltaZeroMap (SSet.ι₁ ≫ h) =
      X ◁ SSet.stdSimplex.δ (0 : Fin 2) ≫ h := by
  rw [tensorDeltaZeroMap, ← Category.assoc, deltaZeroProjection_comp_ι₁]

theorem untensorDeltaZeroMap_restricts
    (i : D ⟶ X) (f : X ⊗ Δ[0] ⟶ Y) (g : D ⊗ Δ[0] ⟶ Y)
    (h : i ▷ Δ[0] ≫ f = g) :
    i ≫ untensorDeltaZeroMap f = untensorDeltaZeroMap g := by
  rw [untensorDeltaZeroMap, untensorDeltaZeroMap, ← Category.assoc,
    ← whiskerRight_deltaZero_section, Category.assoc, h]

/-! ## Elementary horn corrections in a simplicial abelian group -/

variable (A : SimplicialObject AddCommGrpCat.{u})

/-- Correct the `j`th face of an `(n+1)`-simplex, using the `j`th
degeneracy.  This is the elementary operation in the standard proof that
every simplicial abelian group is Kan. -/
def lowerFaceCorrection {n : ℕ} (j : Fin (n + 1))
    (target : (underlyingSSet A).obj
      (op (SimplexCategory.mk n)))
    (y : (underlyingSSet A).obj
      (op (SimplexCategory.mk (n + 1)))) :
    (underlyingSSet A).obj (op (SimplexCategory.mk (n + 1))) :=
  y + (underlyingSSet A).σ j
    (target - (underlyingSSet A).δ j.castSucc y)

@[simp]
theorem lowerFaceCorrection_face_self {n : ℕ} (j : Fin (n + 1))
    (target : (underlyingSSet A).obj
      (op (SimplexCategory.mk n)))
    (y : (underlyingSSet A).obj
      (op (SimplexCategory.mk (n + 1)))) :
    (underlyingSSet A).δ j.castSucc
        (lowerFaceCorrection A j target y) = target := by
  change (A.δ j.castSucc).hom
    (y + (A.σ j).hom (target - (A.δ j.castSucc).hom y)) = target
  calc
    _ = (A.δ j.castSucc).hom y +
        (A.δ j.castSucc).hom
          ((A.σ j).hom (target - (A.δ j.castSucc).hom y)) :=
      (A.δ j.castSucc).hom.map_add _ _
    _ = (A.δ j.castSucc).hom y +
        (target - (A.δ j.castSucc).hom y) := by
      rw [← ConcreteCategory.comp_apply, A.δ_comp_σ_self]
      rfl
    _ = target := by abel

/-- Correct the `j`th face using degeneracy `j-1`; this is the version used
when processing faces from the top down. -/
def upperFaceCorrection {n : ℕ} (j : Fin (n + 2)) (hj : j ≠ 0)
    (target : (underlyingSSet A).obj
      (op (SimplexCategory.mk n)))
    (y : (underlyingSSet A).obj
      (op (SimplexCategory.mk (n + 1)))) :
    (underlyingSSet A).obj (op (SimplexCategory.mk (n + 1))) :=
  let jp : Fin (n + 1) := j.pred hj
  y + (underlyingSSet A).σ jp
    (target - (underlyingSSet A).δ j y)

@[simp]
theorem upperFaceCorrection_face_self {n : ℕ} (j : Fin (n + 2))
    (hj : j ≠ 0)
    (target : (underlyingSSet A).obj
      (op (SimplexCategory.mk n)))
    (y : (underlyingSSet A).obj
      (op (SimplexCategory.mk (n + 1)))) :
    (underlyingSSet A).δ j
        (upperFaceCorrection A j hj target y) = target := by
  let jp : Fin (n + 1) := j.pred hj
  have hj_succ : jp.succ = j := by
    apply Fin.ext
    simp [jp]
  change (A.δ j).hom
    (y + (A.σ jp).hom (target - (A.δ j).hom y)) = target
  calc
    _ = (A.δ j).hom y +
        (A.δ j).hom ((A.σ jp).hom
          (target - (A.δ j).hom y)) :=
      (A.δ j).hom.map_add _ _
    _ = (A.δ j).hom y + (target - (A.δ j).hom y) := by
      rw [← ConcreteCategory.comp_apply, A.δ_comp_σ_succ' hj_succ.symm]
      rfl
    _ = target := by abel

/-- A face strictly below a degeneracy passes through it, with both indices
shifted down in the usual way.  This elementwise form is convenient for the
successive horn-correction construction. -/
theorem face_degeneracy_of_lt {n : ℕ}
    (l : Fin (n + 3)) (j : Fin (n + 2)) (hlt : l.val < j.val)
    (z : (underlyingSSet A).obj (op (SimplexCategory.mk (n + 1)))) :
    (underlyingSSet A).δ l ((underlyingSSet A).σ j z) =
      (underlyingSSet A).σ
        (⟨j.val - 1, by omega⟩ : Fin (n + 1))
        ((underlyingSSet A).δ
          (⟨l.val, by omega⟩ : Fin (n + 2)) z) := by
  let jp : Fin (n + 1) := ⟨j.val - 1, by omega⟩
  let lp : Fin (n + 2) := ⟨l.val, by omega⟩
  have hjpos : 1 ≤ j.val := by omega
  have hj : jp.succ = j := by
    apply Fin.ext
    simp [jp, Nat.sub_add_cancel hjpos]
  have hl : Fin.castSucc lp = l := by
    apply Fin.ext
    rfl
  have hle : lp ≤ Fin.castSucc jp := by
    apply Fin.mk_le_mk.mpr
    change l.val ≤ j.val - 1
    omega
  have hmaps : A.σ j ≫ A.δ l = A.δ lp ≫ A.σ jp := by
    simpa only [hj, hl] using A.δ_comp_σ_of_le hle
  exact ConcreteCategory.congr_hom hmaps z

/-- A face strictly above both faces adjacent to a degeneracy passes through
that degeneracy. -/
theorem face_degeneracy_of_gt_succ {n : ℕ}
    (j : Fin (n + 2)) (l : Fin (n + 3))
    (hlt : j.val + 1 < l.val)
    (z : (underlyingSSet A).obj (op (SimplexCategory.mk (n + 1)))) :
    (underlyingSSet A).δ l ((underlyingSSet A).σ j z) =
      (underlyingSSet A).σ
        (⟨j.val, by omega⟩ : Fin (n + 1))
        ((underlyingSSet A).δ
          (⟨l.val - 1, by omega⟩ : Fin (n + 2)) z) := by
  let jp : Fin (n + 1) := ⟨j.val, by omega⟩
  let lp : Fin (n + 2) := ⟨l.val - 1, by omega⟩
  have hj : Fin.castSucc jp = j := by
    apply Fin.ext
    rfl
  have hl : lp.succ = l := by
    apply Fin.ext
    have hlpos : 1 ≤ l.val := by omega
    simp [lp, Nat.sub_add_cancel hlpos]
  have hgt : Fin.castSucc jp < lp := by
    apply Fin.mk_lt_mk.mpr
    change j.val < l.val - 1
    omega
  have hmaps : A.σ j ≫ A.δ l = A.δ lp ≫ A.σ jp := by
    simpa only [hj, hl] using A.δ_comp_σ_of_gt hgt
  exact ConcreteCategory.congr_hom hmaps z

/-- Successively correct the faces below the missing face `k`.  The argument
`m` records how many faces `0,…,m-1` have been processed. -/
def lowerHornFillAux {n : ℕ} (k : Fin (n + 2))
    (x : Fin (n + 2) →
      (underlyingSSet A).obj (op (SimplexCategory.mk n)))
    (m : ℕ) (hm : m ≤ k.val) :
      (underlyingSSet A).obj (op (SimplexCategory.mk (n + 1))) :=
  match m with
  | 0 => 0
  | m + 1 =>
      lowerFaceCorrection A
        (⟨m, by omega⟩ : Fin (n + 1))
        (x (⟨m, by omega⟩ : Fin (n + 2)))
        (lowerHornFillAux k x m (by omega))

/-- At the successor step, the newly processed face has the prescribed
value. -/
theorem lowerHornFillAux_face_current {n : ℕ} (k : Fin (n + 2))
    (x : Fin (n + 2) →
      (underlyingSSet A).obj (op (SimplexCategory.mk n)))
    (m : ℕ) (hm : m + 1 ≤ k.val) :
    (underlyingSSet A).δ (⟨m, by omega⟩ : Fin (n + 2))
        (lowerHornFillAux A k x (m + 1) hm) =
      x (⟨m, by omega⟩ : Fin (n + 2)) := by
  let jd : Fin (n + 1) := ⟨m, by omega⟩
  let jf : Fin (n + 2) := ⟨m, by omega⟩
  have hcast : jd.castSucc = jf := by
    apply Fin.ext
    rfl
  change (underlyingSSet A).δ jf
      (lowerFaceCorrection A jd (x jf)
        (lowerHornFillAux A k x m (by omega))) = x jf
  rw [← hcast]
  exact lowerFaceCorrection_face_self A jd (x jf)
    (lowerHornFillAux A k x m (by omega))

/-- Compatibility of the codimension-one faces of a positive-dimensional
horn, stated directly on its simplex values. -/
def HornFaceCompatibleSucc {n : ℕ} (k : Fin (n + 3))
    (x : Fin (n + 3) →
      (underlyingSSet A).obj (op (SimplexCategory.mk (n + 1)))) : Prop :=
  ∀ (a b : Fin (n + 3)) (_ha : a ≠ k) (_hb : b ≠ k) (hab : a < b),
    (underlyingSSet A).δ (b.pred (Fin.ne_zero_of_lt hab)) (x a) =
      (underlyingSSet A).δ (a.castPred (Fin.ne_last_of_lt hab)) (x b)

/-- A lower correction does not disturb an already corrected earlier face,
provided the prescribed faces satisfy the horn compatibility equations. -/
theorem lowerFaceCorrection_preserves_earlier {n : ℕ}
    (k : Fin (n + 3))
    (x : Fin (n + 3) →
      (underlyingSSet A).obj (op (SimplexCategory.mk (n + 1))))
    (hcompat : HornFaceCompatibleSucc A k x)
    (j : Fin (n + 2)) (hjk : j.castSucc < k)
    (l : Fin (n + 3)) (hlj : l.val < j.val)
    (y : (underlyingSSet A).obj (op (SimplexCategory.mk (n + 2))))
    (hy : (underlyingSSet A).δ l y = x l) :
    (underlyingSSet A).δ l
        (lowerFaceCorrection A j (x j.castSucc) y) = x l := by
  let lp : Fin (n + 2) := ⟨l.val, by omega⟩
  let jp : Fin (n + 2) := ⟨j.val - 1, by omega⟩
  have hjpos : 1 ≤ j.val := by omega
  have hJne : j.castSucc ≠ k := ne_of_lt hjk
  have hLJ : l < j.castSucc := Fin.mk_lt_mk.mpr hlj
  have hLne : l ≠ k := ne_of_lt (hLJ.trans hjk)
  have hcompat' := hcompat l j.castSucc hLne hJne hLJ
  have hlp : l.castPred (Fin.ne_last_of_lt hLJ) = lp := by
    apply Fin.ext
    rfl
  have hjp : (j.castSucc).pred (Fin.ne_zero_of_lt hLJ) = jp := by
    apply Fin.ext
    simp [jp]
  have hlcast : lp.castSucc = l := by
    apply Fin.ext
    rfl
  have hjsucc : jp.succ = j.castSucc := by
    apply Fin.ext
    simp [jp, Nat.sub_add_cancel hjpos]
  have hlpj : lp ≤ jp := by
    apply Fin.mk_le_mk.mpr
    omega
  have hfaces :
      (underlyingSSet A).δ lp
          ((underlyingSSet A).δ j.castSucc y) =
        (underlyingSSet A).δ jp
          ((underlyingSSet A).δ l y) := by
    have h := (underlyingSSet A).δ_comp_δ_apply hlpj y
    simpa only [hjsucc, hlcast] using h
  have hcompatA :
      (A.δ jp).hom (x l) = (A.δ lp).hom (x j.castSucc) := by
    change (A.δ ((j.castSucc).pred (Fin.ne_zero_of_lt hLJ))).hom (x l) =
      (A.δ (l.castPred (Fin.ne_last_of_lt hLJ))).hom (x j.castSucc) at hcompat'
    simpa only [hjp, hlp] using hcompat'
  have hfacesA :
      (A.δ lp).hom ((A.δ j.castSucc).hom y) =
        (A.δ jp).hom ((A.δ l).hom y) := by
    exact hfaces
  have hyA : (A.δ l).hom y = x l := by
    exact hy
  have hdiff :
      (underlyingSSet A).δ lp
          (x j.castSucc - (underlyingSSet A).δ j.castSucc y) = 0 := by
    change (A.δ lp).hom
      (x j.castSucc - (A.δ j.castSucc).hom y) = 0
    calc
      _ = (A.δ lp).hom (x j.castSucc) -
          (A.δ lp).hom ((A.δ j.castSucc).hom y) :=
        (A.δ lp).hom.map_sub _ _
      _ = (A.δ jp).hom (x l) -
          (A.δ jp).hom ((A.δ l).hom y) := by
        rw [← hcompatA, hfacesA]
      _ = 0 := by rw [hyA]; simp
  have hdegzero :
      (underlyingSSet A).δ l
          ((underlyingSSet A).σ j
            (x j.castSucc - (underlyingSSet A).δ j.castSucc y)) = 0 := by
    rw [face_degeneracy_of_lt A l j hlj]
    rw [hdiff]
    exact (A.σ (⟨j.val - 1, by omega⟩ : Fin (n + 1))).hom.map_zero
  have hdegzeroA :
      (A.δ l).hom ((A.σ j).hom
        (x j.castSucc - (A.δ j.castSucc).hom y)) = 0 := by
    exact hdegzero
  change (A.δ l).hom
    (y + (A.σ j).hom (x j.castSucc - (A.δ j.castSucc).hom y)) = x l
  calc
    _ = (A.δ l).hom y +
        (A.δ l).hom ((A.σ j).hom
          (x j.castSucc - (A.δ j.castSucc).hom y)) :=
      (A.δ l).hom.map_add _ _
    _ = x l + 0 := by rw [hyA, hdegzeroA]; rfl
    _ = x l := add_zero _

/-- After `m` lower-correction steps, every face with index below `m` has
the prescribed horn value. -/
theorem lowerHornFillAux_faces {n : ℕ} (k : Fin (n + 3))
    (x : Fin (n + 3) →
      (underlyingSSet A).obj (op (SimplexCategory.mk (n + 1))))
    (hcompat : HornFaceCompatibleSucc A k x)
    (m : ℕ) (hm : m ≤ k.val)
    (l : Fin (n + 3)) (hlm : l.val < m) :
    (underlyingSSet A).δ l (lowerHornFillAux A k x m hm) = x l := by
  induction m with
  | zero => omega
  | succ m ih =>
      by_cases hl : l.val = m
      · let jf : Fin (n + 3) := ⟨m, by omega⟩
        have hljf : l = jf := by
          apply Fin.ext
          exact hl
        simpa only [hljf] using
          lowerHornFillAux_face_current A k x m hm
      · have hlm' : l.val < m := by omega
        let j : Fin (n + 2) := ⟨m, by omega⟩
        have hjk : j.castSucc < k := by
          apply Fin.mk_lt_mk.mpr
          change m < k.val
          omega
        change (underlyingSSet A).δ l
          (lowerFaceCorrection A j (x j.castSucc)
            (lowerHornFillAux A k x m (by omega))) = x l
        exact lowerFaceCorrection_preserves_earlier A k x hcompat
          j hjk l (by simpa [j] using hlm')
          (lowerHornFillAux A k x m (by omega))
          (ih (by omega) hlm')

/-- Starting from `y₀`, successively correct the faces above the missing
face `k`, beginning with the top face and moving downwards. -/
def upperHornFillAux {n : ℕ} (k : Fin (n + 2))
    (x : Fin (n + 2) →
      (underlyingSSet A).obj (op (SimplexCategory.mk n)))
    (y₀ : (underlyingSSet A).obj (op (SimplexCategory.mk (n + 1))))
    (r : ℕ) (hr : r ≤ n + 1 - k.val) :
      (underlyingSSet A).obj (op (SimplexCategory.mk (n + 1))) :=
  match r with
  | 0 => y₀
  | r + 1 =>
      let J : Fin (n + 2) := ⟨n + 1 - r, by omega⟩
      upperFaceCorrection A J (by
        apply Fin.ne_of_gt
        change 0 < n + 1 - r
        apply Nat.sub_pos_of_lt
        exact Nat.lt_of_succ_le
          (hr.trans (Nat.sub_le (n + 1) k.val)))
        (x J) (upperHornFillAux k x y₀ r (by omega))

/-- At each upper-correction step, the newly processed face acquires its
prescribed value. -/
theorem upperHornFillAux_face_current {n : ℕ} (k : Fin (n + 2))
    (x : Fin (n + 2) →
      (underlyingSSet A).obj (op (SimplexCategory.mk n)))
    (y₀ : (underlyingSSet A).obj (op (SimplexCategory.mk (n + 1))))
    (r : ℕ) (hr : r + 1 ≤ n + 1 - k.val) :
    let J : Fin (n + 2) := ⟨n + 1 - r, by omega⟩
    (underlyingSSet A).δ J
        (upperHornFillAux A k x y₀ (r + 1) hr) = x J := by
  let J : Fin (n + 2) := ⟨n + 1 - r, by omega⟩
  have hJzero : J ≠ 0 := by
    apply Fin.ne_of_gt
    exact Fin.mk_lt_mk.mpr (by dsimp [J]; omega)
  change (underlyingSSet A).δ J
      (upperFaceCorrection A J hJzero (x J)
        (upperHornFillAux A k x y₀ r (by omega))) = x J
  exact upperFaceCorrection_face_self A J hJzero (x J)
    (upperHornFillAux A k x y₀ r (by omega))

/-- An upper correction preserves every already corrected face above it. -/
theorem upperFaceCorrection_preserves_later {n : ℕ}
    (k : Fin (n + 3))
    (x : Fin (n + 3) →
      (underlyingSSet A).obj (op (SimplexCategory.mk (n + 1))))
    (hcompat : HornFaceCompatibleSucc A k x)
    (J : Fin (n + 3)) (hkJ : k < J)
    (l : Fin (n + 3)) (hJl : J < l)
    (y : (underlyingSSet A).obj (op (SimplexCategory.mk (n + 2))))
    (hy : (underlyingSSet A).δ l y = x l) :
    (underlyingSSet A).δ l
        (upperFaceCorrection A J
          (ne_of_gt ((Fin.zero_le k).trans_lt hkJ))
          (x J) y) = x l := by
  have hJzero : J ≠ 0 := ne_of_gt ((Fin.zero_le k).trans_lt hkJ)
  let jd : Fin (n + 2) := J.pred hJzero
  have hlzero : l ≠ 0 := ne_of_gt ((Fin.zero_le J).trans_lt hJl)
  let lp : Fin (n + 2) := l.pred hlzero
  let Js : Fin (n + 2) := J.castPred (Fin.ne_last_of_lt hJl)
  have hJne : J ≠ k := ne_of_gt hkJ
  have hlne : l ≠ k := ne_of_gt (hkJ.trans hJl)
  have hc := hcompat J l hJne hlne hJl
  have hjd : J.pred hJzero = jd := rfl
  have hlp : l.pred (Fin.ne_zero_of_lt hJl) = lp := by
    apply Fin.ext
    rfl
  have hJs : J.castPred (Fin.ne_last_of_lt hJl) = Js := rfl
  have hjdsucc : jd.succ = J := by
    apply Fin.ext
    simp [jd]
  have hJscast : Js.castSucc = J := by
    apply Fin.ext
    rfl
  have hJslelp : Js ≤ lp := by
    apply Fin.mk_le_mk.mpr
    change J.val ≤ l.val - 1
    omega
  have hlpsucc : lp.succ = l := by
    apply Fin.ext
    simp [lp]
  have hfaces :
      (underlyingSSet A).δ lp
          ((underlyingSSet A).δ J y) =
        (underlyingSSet A).δ Js
          ((underlyingSSet A).δ l y) := by
    have h := (underlyingSSet A).δ_comp_δ_apply hJslelp y
    -- `h` has the opposite orientation to the displayed equality.
    simpa only [hlpsucc, hJscast] using h.symm
  have hcA : (A.δ lp).hom (x J) = (A.δ Js).hom (x l) := by
    change (A.δ (l.pred (Fin.ne_zero_of_lt hJl))).hom (x J) =
      (A.δ (J.castPred (Fin.ne_last_of_lt hJl))).hom (x l) at hc
    simpa only [hlp, hJs] using hc
  have hfacesA :
      (A.δ lp).hom ((A.δ J).hom y) =
        (A.δ Js).hom ((A.δ l).hom y) := by
    exact hfaces
  have hyA : (A.δ l).hom y = x l := by exact hy
  have hdiff :
      (underlyingSSet A).δ lp
        (x J - (underlyingSSet A).δ J y) = 0 := by
    change (A.δ lp).hom (x J - (A.δ J).hom y) = 0
    calc
      _ = (A.δ lp).hom (x J) -
          (A.δ lp).hom ((A.δ J).hom y) :=
        (A.δ lp).hom.map_sub _ _
      _ = (A.δ Js).hom (x l) -
          (A.δ Js).hom ((A.δ l).hom y) := by
        rw [hcA, hfacesA]
      _ = 0 := by rw [hyA]; simp
  have hdegzero :
      (underlyingSSet A).δ l
        ((underlyingSSet A).σ jd
          (x J - (underlyingSSet A).δ J y)) = 0 := by
    rw [face_degeneracy_of_gt_succ A jd l (by dsimp [jd]; omega)]
    have hlpbound : l.val - 1 < n + 2 := by omega
    have hlpval : (⟨l.val - 1, hlpbound⟩ : Fin (n + 2)) = lp := by
      apply Fin.ext
      rfl
    rw [hlpval, hdiff]
    have hJval : J.val < l.val := hJl
    have hlval : l.val < n + 3 := l.isLt
    have hjdbound : jd.val < n + 1 := by
      dsimp [jd]
      omega
    exact (A.σ (⟨jd.val, hjdbound⟩ : Fin (n + 1))).hom.map_zero
  have hdegzeroA :
      (A.δ l).hom ((A.σ jd).hom
        (x J - (A.δ J).hom y)) = 0 := by exact hdegzero
  change (A.δ l).hom
    (y + (A.σ jd).hom (x J - (A.δ J).hom y)) = x l
  calc
    _ = (A.δ l).hom y + (A.δ l).hom
        ((A.σ jd).hom (x J - (A.δ J).hom y)) :=
      (A.δ l).hom.map_add _ _
    _ = x l + 0 := by rw [hyA, hdegzeroA]; rfl
    _ = x l := add_zero _

/-- An upper correction also preserves all faces below the missing face. -/
theorem upperFaceCorrection_preserves_lower {n : ℕ}
    (k : Fin (n + 3))
    (x : Fin (n + 3) →
      (underlyingSSet A).obj (op (SimplexCategory.mk (n + 1))))
    (hcompat : HornFaceCompatibleSucc A k x)
    (J : Fin (n + 3)) (hkJ : k < J)
    (l : Fin (n + 3)) (hlk : l < k)
    (y : (underlyingSSet A).obj (op (SimplexCategory.mk (n + 2))))
    (hy : (underlyingSSet A).δ l y = x l) :
    (underlyingSSet A).δ l
        (upperFaceCorrection A J
          (ne_of_gt ((Fin.zero_le k).trans_lt hkJ)) (x J) y) = x l := by
  have hJzero : J ≠ 0 := ne_of_gt ((Fin.zero_le k).trans_lt hkJ)
  let jd : Fin (n + 2) := J.pred hJzero
  let lp : Fin (n + 2) := l.castPred
    (Fin.ne_last_of_lt (hlk.trans hkJ))
  have hlJ : l < J := hlk.trans hkJ
  have hlne : l ≠ k := ne_of_lt hlk
  have hJne : J ≠ k := ne_of_gt hkJ
  have hc := hcompat l J hlne hJne hlJ
  have hjd : J.pred (Fin.ne_zero_of_lt hlJ) = jd := by
    apply Fin.ext
    rfl
  have hlp : l.castPred (Fin.ne_last_of_lt hlJ) = lp := by
    apply Fin.ext
    rfl
  have hjdsucc : jd.succ = J := by
    apply Fin.ext
    simp [jd]
  have hlpcast : lp.castSucc = l := by
    apply Fin.ext
    rfl
  have hlpjd : lp ≤ jd := by
    apply Fin.mk_le_mk.mpr
    change l.val ≤ J.val - 1
    omega
  have hfaces :
      (underlyingSSet A).δ lp
          ((underlyingSSet A).δ J y) =
        (underlyingSSet A).δ jd
          ((underlyingSSet A).δ l y) := by
    have h := (underlyingSSet A).δ_comp_δ_apply hlpjd y
    simpa only [hjdsucc, hlpcast] using h
  have hcA : (A.δ jd).hom (x l) = (A.δ lp).hom (x J) := by
    change (A.δ (J.pred (Fin.ne_zero_of_lt hlJ))).hom (x l) =
      (A.δ (l.castPred (Fin.ne_last_of_lt hlJ))).hom (x J) at hc
    simpa only [hjd, hlp] using hc
  have hfacesA :
      (A.δ lp).hom ((A.δ J).hom y) =
        (A.δ jd).hom ((A.δ l).hom y) := by exact hfaces
  have hyA : (A.δ l).hom y = x l := by exact hy
  have hdiff :
      (underlyingSSet A).δ lp
        (x J - (underlyingSSet A).δ J y) = 0 := by
    change (A.δ lp).hom (x J - (A.δ J).hom y) = 0
    calc
      _ = (A.δ lp).hom (x J) -
          (A.δ lp).hom ((A.δ J).hom y) :=
        (A.δ lp).hom.map_sub _ _
      _ = (A.δ jd).hom (x l) -
          (A.δ jd).hom ((A.δ l).hom y) := by
        rw [← hcA, hfacesA]
      _ = 0 := by rw [hyA]; simp
  have hdegzero :
      (underlyingSSet A).δ l
        ((underlyingSSet A).σ jd
          (x J - (underlyingSSet A).δ J y)) = 0 := by
    have hljd : l.val < jd.val := by
      dsimp [jd]
      omega
    rw [face_degeneracy_of_lt A l jd hljd]
    have hlpval : (⟨l.val, by omega⟩ : Fin (n + 2)) = lp := by
      apply Fin.ext
      rfl
    rw [hlpval, hdiff]
    have hjdval : jd.val - 1 < n + 1 := by omega
    exact (A.σ (⟨jd.val - 1, hjdval⟩ : Fin (n + 1))).hom.map_zero
  have hdegzeroA :
      (A.δ l).hom ((A.σ jd).hom
        (x J - (A.δ J).hom y)) = 0 := by exact hdegzero
  change (A.δ l).hom
    (y + (A.σ jd).hom (x J - (A.δ J).hom y)) = x l
  calc
    _ = (A.δ l).hom y + (A.δ l).hom
        ((A.σ jd).hom (x J - (A.δ J).hom y)) :=
      (A.δ l).hom.map_add _ _
    _ = x l + 0 := by rw [hyA, hdegzeroA]; rfl
    _ = x l := add_zero _

/-- The descending correction stage preserves all faces below the missing
face. -/
theorem upperHornFillAux_lower_faces {n : ℕ} (k : Fin (n + 3))
    (x : Fin (n + 3) →
      (underlyingSSet A).obj (op (SimplexCategory.mk (n + 1))))
    (hcompat : HornFaceCompatibleSucc A k x)
    (y₀ : (underlyingSSet A).obj (op (SimplexCategory.mk (n + 2))))
    (hy₀ : ∀ l : Fin (n + 3), l < k →
      (underlyingSSet A).δ l y₀ = x l)
    (r : ℕ) (hr : r ≤ n + 2 - k.val)
    (l : Fin (n + 3)) (hlk : l < k) :
    (underlyingSSet A).δ l
        (upperHornFillAux A k x y₀ r hr) = x l := by
  induction r with
  | zero => exact hy₀ l hlk
  | succ r ih =>
      let J : Fin (n + 3) := ⟨n + 2 - r, by omega⟩
      have hk : k.val ≤ n + 2 := by omega
      have hsub := Nat.sub_add_cancel hk
      have hkJ : k < J := by
        apply Fin.mk_lt_mk.mpr
        omega
      have hJzero : J ≠ 0 := ne_of_gt ((Fin.zero_le k).trans_lt hkJ)
      change (underlyingSSet A).δ l
        (upperFaceCorrection A J hJzero (x J)
          (upperHornFillAux A k x y₀ r (by omega))) = x l
      exact upperFaceCorrection_preserves_lower A k x hcompat
        J hkJ l hlk (upperHornFillAux A k x y₀ r (by omega))
        (ih (by omega))

/-- After `r` descending steps, every face strictly above the current
threshold `n+2-r` has the prescribed value. -/
theorem upperHornFillAux_high_faces {n : ℕ} (k : Fin (n + 3))
    (x : Fin (n + 3) →
      (underlyingSSet A).obj (op (SimplexCategory.mk (n + 1))))
    (hcompat : HornFaceCompatibleSucc A k x)
    (y₀ : (underlyingSSet A).obj (op (SimplexCategory.mk (n + 2))))
    (r : ℕ) (hr : r ≤ n + 2 - k.val)
    (l : Fin (n + 3)) (hl : n + 2 - r < l.val) :
    (underlyingSSet A).δ l
        (upperHornFillAux A k x y₀ r hr) = x l := by
  induction r with
  | zero => omega
  | succ r ih =>
      let J : Fin (n + 3) := ⟨n + 2 - r, by omega⟩
      have hk : k.val ≤ n + 2 := by omega
      have hsub := Nat.sub_add_cancel hk
      have hkJ : k < J := by
        apply Fin.mk_lt_mk.mpr
        omega
      have hJzero : J ≠ 0 := ne_of_gt ((Fin.zero_le k).trans_lt hkJ)
      by_cases hlJ : l = J
      · simpa only [hlJ] using
          upperHornFillAux_face_current A k x y₀ r hr
      · have hJl : J < l := by
          apply Fin.mk_lt_mk.mpr
          have hpos : 0 < n + 2 - r := by
            change 0 < J.val
            exact Fin.pos_iff_ne_zero.mpr hJzero
          have hstep : n + 2 - r = (n + 2 - (r + 1)) + 1 := by
            rw [show r + 1 = r.succ by omega, Nat.sub_succ]
            symm
            simpa [Nat.succ_eq_add_one] using Nat.succ_pred_eq_of_pos hpos
          have hlJval : l.val ≠ n + 2 - r := by
            intro heq
            apply hlJ
            apply Fin.ext
            simpa [J] using heq
          omega
        change (underlyingSSet A).δ l
          (upperFaceCorrection A J hJzero (x J)
            (upperHornFillAux A k x y₀ r (by omega))) = x l
        exact upperFaceCorrection_preserves_later A k x hcompat
          J hkJ l hJl (upperHornFillAux A k x y₀ r (by omega))
          (ih (by omega) (by omega))

/-! ## The standard Kan filler for a simplicial abelian group -/

/-- The filler produced by first fixing the faces below the missing face and
then fixing the faces above it in descending order. -/
def abelianHornFillSucc {n : ℕ} (k : Fin (n + 3))
    (x : Fin (n + 3) →
      (underlyingSSet A).obj (op (SimplexCategory.mk (n + 1)))) :
    (underlyingSSet A).obj (op (SimplexCategory.mk (n + 2))) :=
  let lower := lowerHornFillAux A k x k.val le_rfl
  upperHornFillAux A k x lower (n + 2 - k.val) le_rfl

/-- The explicit abelian-group filler has every prescribed face. -/
theorem abelianHornFillSucc_faces {n : ℕ} (k : Fin (n + 3))
    (x : Fin (n + 3) →
      (underlyingSSet A).obj (op (SimplexCategory.mk (n + 1))))
    (hcompat : HornFaceCompatibleSucc A k x)
    (l : Fin (n + 3)) (hl : l ≠ k) :
    (underlyingSSet A).δ l (abelianHornFillSucc A k x) = x l := by
  have hk : k.val ≤ n + 2 := by omega
  by_cases hlk : l < k
  · apply upperHornFillAux_lower_faces A k x hcompat
      (lowerHornFillAux A k x k.val le_rfl)
    · intro j hjk
      apply lowerHornFillAux_faces A k x hcompat k.val le_rfl j
      exact Fin.mk_lt_mk.mp hjk
    · exact hlk
  · have hkl : k < l := by
      apply Fin.mk_lt_mk.mpr
      have hne : l.val ≠ k.val := by
        intro h
        apply hl
        exact Fin.ext h
      omega
    apply upperHornFillAux_high_faces A k x hcompat
      (lowerHornFillAux A k x k.val le_rfl)
      (n + 2 - k.val) le_rfl l
    rw [Nat.sub_sub_self hk]
    exact Fin.mk_lt_mk.mp hkl

/-- Replace the absent face of a horn by zero, obtaining a total family of
simplex values.  The absent entry is never used by the filler identities. -/
def hornFaceValuesSucc {n : ℕ} {k : Fin (n + 3)}
    (f : ∀ (j : Fin (n + 3)) (_ : j ≠ k),
      Δ[n + 1] ⟶ underlyingSSet A) :
    Fin (n + 3) →
      (underlyingSSet A).obj (op (SimplexCategory.mk (n + 1))) :=
  fun j ↦ if hj : j = k then 0 else SSet.yonedaEquiv (f j hj)

@[simp]
theorem hornFaceValuesSucc_of_ne {n : ℕ} {k : Fin (n + 3)}
    (f : ∀ (j : Fin (n + 3)) (_ : j ≠ k),
      Δ[n + 1] ⟶ underlyingSSet A)
    (j : Fin (n + 3)) (hj : j ≠ k) :
    hornFaceValuesSucc A f j = SSet.yonedaEquiv (f j hj) := by
  simp only [hornFaceValuesSucc, dite_eq_right hj]

/-- Compatibility of a positive-dimensional horn, transferred through the
Yoneda equivalence to the elementwise compatibility used by the correction
algorithm. -/
theorem hornFaceValuesSucc_compatible {n : ℕ} {k : Fin (n + 3)}
    (f : ∀ (j : Fin (n + 3)) (_ : j ≠ k),
      Δ[n + 1] ⟶ underlyingSSet A)
    (hf : horn.IsCompatible f) :
    HornFaceCompatibleSucc A k (hornFaceValuesSucc A f) := by
  intro a b ha hb hab
  rw [hornFaceValuesSucc_of_ne A f a ha,
    hornFaceValuesSucc_of_ne A f b hb]
  have h := congrArg SSet.yonedaEquiv
    (hf.δ_pred_comp a b ha hb hab)
  simpa only [SSet.stdSimplex.yonedaEquiv_δ_comp] using h

/-- The standard explicit filler of a positive-dimensional horn in a
simplicial abelian group, expressed as a map from the standard simplex. -/
def abelianHornLiftSucc {n : ℕ} {k : Fin (n + 3)}
    (f : ∀ (j : Fin (n + 3)) (_ : j ≠ k),
      Δ[n + 1] ⟶ underlyingSSet A) :
    Δ[n + 2] ⟶ underlyingSSet A :=
  SSet.yonedaEquiv.symm
    (abelianHornFillSucc A k (hornFaceValuesSucc A f))

@[reassoc]
theorem abelianHornLiftSucc_faces {n : ℕ} {k : Fin (n + 3)}
    (f : ∀ (j : Fin (n + 3)) (_ : j ≠ k),
      Δ[n + 1] ⟶ underlyingSSet A)
    (hf : horn.IsCompatible f)
    (j : Fin (n + 3)) (hj : j ≠ k) :
    SSet.stdSimplex.δ j ≫ abelianHornLiftSucc A f = f j hj := by
  rw [abelianHornLiftSucc,
    SSet.stdSimplex.δ_comp_yonedaEquiv_symm,
    abelianHornFillSucc_faces A k (hornFaceValuesSucc A f)
      (hornFaceValuesSucc_compatible A f hf) j hj,
    hornFaceValuesSucc_of_ne A f j hj,
    Equiv.symm_apply_apply]

/-- Every underlying simplicial set of a simplicial abelian group is a Kan
complex.  This theorem is standard, but is proved here because the Mathlib
revision used by the project does not yet expose the corresponding instance. -/
theorem underlyingSSet_isKan : KanComplex (underlyingSSet A) := by
  rw [SSet.KanComplex.iff]
  intro n k f hf
  cases n with
  | zero =>
      fin_cases k
      · refine ⟨SSet.stdSimplex.σ (0 : Fin 1) ≫ f 1 (by decide), ?_⟩
        intro j hj
        fin_cases j
        · exact (hj rfl).elim
        · rw [← Category.assoc]
          change (SSet.stdSimplex.δ (Fin.succ (0 : Fin 1)) ≫
            SSet.stdSimplex.σ (0 : Fin 1)) ≫ f 1 (by decide) =
              f 1 hj
          rw [SSet.stdSimplex.δ_comp_σ_succ]
          simp
      · refine ⟨SSet.stdSimplex.σ (0 : Fin 1) ≫ f 0 (by decide), ?_⟩
        intro j hj
        fin_cases j
        · rw [← Category.assoc]
          change (SSet.stdSimplex.δ (Fin.castSucc (0 : Fin 1)) ≫
            SSet.stdSimplex.σ (0 : Fin 1)) ≫ f 0 (by decide) =
              f 0 hj
          rw [SSet.stdSimplex.δ_comp_σ_self]
          simp
        · exact (hj rfl).elim
  | succ n =>
      exact ⟨abelianHornLiftSucc A f,
        abelianHornLiftSucc_faces A f hf⟩

instance underlyingSSet_kanComplex : KanComplex (underlyingSSet A) :=
  underlyingSSet_isKan A

end GeneralSphereT.Section4.NativeConeCriterionReverse

namespace GeneralSphereT.SimplicialCochain

open GeneralSphereT.Section4
open GeneralSphereT.Section4.UnderlyingSSet
open GeneralSphereT.Section4.RelativeMapping
open GeneralSphereT.Section4.NativeRelativeHomotopyGroup
open GeneralSphereT.Section4.NativeConeCriterionReverse

variable {V : Type u} [LinearOrder V] [Fintype V]

local instance (priority := 10000) nativeConeReverseOptionLE : LE (Option V) :=
  @WithBot.instLE V inferInstance

local instance (priority := 10000) nativeConeReverseOptionLT : LT (Option V) :=
  @WithBot.instLT V inferInstance

local instance (priority := 10000) nativeConeReverseOptionLinearOrder :
    LinearOrder (Option V) :=
  @WithBot.linearOrder V inferInstance

omit [Fintype V] in
@[reassoc]
theorem ι₀_literalConeBaseLineMap_reverse
    (M : AbstractSimplicialComplex V) (b : V) :
    SSet.ι₀ ≫ literalConeBaseLineMap M b =
      SSet.const (literalConeApex M) := by
  rw [literalConeBaseLineMap, ← Category.assoc, SSet.ι₀_comp,
    Category.assoc, ι₀_literalConeCylinderMap, SSet.comp_const]

omit [Fintype V] in
/-- Vanishing on the basepoint line already includes vanishing at the
literal cone apex. -/
theorem literalConeApex_comp_eq_zero_of_baseLine_reverse
    (M : AbstractSimplicialComplex V) (b : V)
    (A : SimplicialObject AddCommGrpCat.{u})
    (f : orderedComplexSSet (simplicialCone M) ⟶ underlyingSSet A)
    (hbase : literalConeBaseLineMap M b ≫ f = 0) :
    SSet.const
        (X := orderedComplexSSet (simplicialCone M))
        (literalConeApex M) ≫ f = 0 := by
  have hconstBase :
      SSet.const
          (X := (orderedComplexBasepointSubcomplex M b : SSet))
          (literalConeApex M) ≫ f = 0 := by
    rw [← ι₀_literalConeBaseLineMap_reverse M b, Category.assoc, hbase]
    ext Δ z
    rfl
  let p :
      (orderedComplexBasepointSubcomplex M b : SSet).obj
        (Opposite.op (SimplexCategory.mk 0)) :=
    ⟨orderedComplexVertex M b,
      SSet.Subcomplex.mem_ofSimplex_obj (orderedComplexVertex M b)⟩
  have hapex :
      f.app (Opposite.op (SimplexCategory.mk 0)) (literalConeApex M) = 0 := by
    have hp := ConcreteCategory.congr_hom
      (congr_app hconstBase (Opposite.op (SimplexCategory.mk 0))) p
    exact hp
  rw [SSet.const_comp, hapex]
  exact const_zeroVertex_eq_zeroMap
    (X := orderedComplexSSet (simplicialCone M)) A

/-- Final assembly after homotopy extension, still stated for the map with
an inessential `Delta[0]` source factor. -/
def literalPointedExtensionOfTensorDeltaZeroMap
    (M : AbstractSimplicialComplex V) (b : V)
    (A : SimplicialObject AddCommGrpCat.{u})
    (f : NativeRelativeMorphism
      (orderedComplexBasepointSubcomplex M b) A)
    (g : orderedComplexSSet (simplicialCone M) ⊗ Δ[0] ⟶ underlyingSSet A)
    (hbottom :
      literalConeBottomMap M ▷ Δ[0] ≫ g =
        tensorDeltaZeroMap f.map)
    (hbase :
      literalConeBaseLineMap M b ▷ Δ[0] ≫ g = 0) :
    LiteralPointedExtension M b A f where
  map := untensorDeltaZeroMap g
  bottom := by
    rw [untensorDeltaZeroMap_restricts
      (literalConeBottomMap M) g (tensorDeltaZeroMap f.map) hbottom,
      untensor_tensorDeltaZeroMap]
  baseLine := by
    rw [untensorDeltaZeroMap, ← Category.assoc,
      ← whiskerRight_deltaZero_section, Category.assoc, hbase]
    ext Δ z
    rfl
  apex := literalConeApex_comp_eq_zero_of_baseLine_reverse M b A
    (untensorDeltaZeroMap g) (by
      rw [untensorDeltaZeroMap, ← Category.assoc,
        ← whiskerRight_deltaZero_section, Category.assoc, hbase]
      ext Δ z
      rfl)

/-! ## From a native relative nullhomotopy to a literal cone extension -/

omit [Fintype V] in
theorem nativeNullhomotopy_rel_eq_zero
    (M : AbstractSimplicialComplex V) (b : V)
    (A : SimplicialObject AddCommGrpCat.{u})
    {f : NativeRelativeMorphism
      (orderedComplexBasepointSubcomplex M b) A}
    (H : SSet.RelativeMorphism.Homotopy
      (0 : NativeRelativeMorphism
        (orderedComplexBasepointSubcomplex M b) A) f) :
    (orderedComplexBasepointSubcomplex M b).ι ▷ Δ[1] ≫ H.h = 0 := by
  calc
    _ = fst (orderedComplexBasepointSubcomplex M b : SSet) Δ[1] ≫
          zeroBoundary (orderedComplexBasepointSubcomplex M b) A ≫
            (zeroSubcomplex A).ι := H.rel
    _ = 0 := cylinder_zeroBoundary
      (orderedComplexBasepointSubcomplex M b) A

omit [Fintype V] in
theorem nativeNullhomotopy_initial_eq_zero
    (M : AbstractSimplicialComplex V) (b : V)
    (A : SimplicialObject AddCommGrpCat.{u})
    {f : NativeRelativeMorphism
      (orderedComplexBasepointSubcomplex M b) A}
    (H : SSet.RelativeMorphism.Homotopy
      (0 : NativeRelativeMorphism
        (orderedComplexBasepointSubcomplex M b) A) f) :
    SSet.ι₀ ≫ H.h = 0 := by
  exact H.h₀.trans
    (relativeMorphism_zero_map
      (orderedComplexBasepointSubcomplex M b) A)

/-- Glue the given homotopy to zero on the basepoint cone.  Its domain is
the union of the bottom and the basepoint line inside the literal cone. -/
noncomputable def nativeNullhomotopyBoundaryPath
    (M : AbstractSimplicialComplex V) (b : V)
    (A : SimplicialObject AddCommGrpCat.{u})
    {f : NativeRelativeMorphism
      (orderedComplexBasepointSubcomplex M b) A}
    (H : SSet.RelativeMorphism.Homotopy
      (0 : NativeRelativeMorphism
        (orderedComplexBasepointSubcomplex M b) A) f) :
    (literalConeBoundarySubcomplex M b : SSet) ⊗ Δ[1] ⟶
      underlyingSSet A :=
  literalConeBoundaryHomotopy M b A H.h
    (nativeNullhomotopy_rel_eq_zero M b A H)

omit [Fintype V] in
theorem nativeNullhomotopyBoundaryPath_initial
    (M : AbstractSimplicialComplex V) (b : V)
    (A : SimplicialObject AddCommGrpCat.{u})
    {f : NativeRelativeMorphism
      (orderedComplexBasepointSubcomplex M b) A}
    (H : SSet.RelativeMorphism.Homotopy
      (0 : NativeRelativeMorphism
        (orderedComplexBasepointSubcomplex M b) A) f) :
    (literalConeBoundarySubcomplex M b).ι ▷ Δ[0] ≫
        tensorDeltaZeroMap
          (0 : orderedComplexSSet (simplicialCone M) ⟶ underlyingSSet A) =
      (literalConeBoundarySubcomplex M b : SSet) ◁
          SSet.stdSimplex.δ (1 : Fin 2) ≫
        nativeNullhomotopyBoundaryPath M b A H := by
  calc
    _ = 0 := by ext Δ z; rfl
    _ = (literalConeBoundarySubcomplex M b : SSet) ◁
          SSet.stdSimplex.δ (1 : Fin 2) ≫
        literalConeBoundaryHomotopy M b A H.h
          (nativeNullhomotopy_rel_eq_zero M b A H) :=
      (literalConeBoundaryHomotopy_hep_initial M b A H.h
        (nativeNullhomotopy_rel_eq_zero M b A H)
        (nativeNullhomotopy_initial_eq_zero M b A H)).symm

/-- Lift the boundary path along the internal-Hom restriction fibration and
take its terminal endpoint. -/
noncomputable def nativeNullhomotopyExtendedTerminalMap
    (M : AbstractSimplicialComplex V) (b : V)
    (A : SimplicialObject AddCommGrpCat.{u})
    {f : NativeRelativeMorphism
      (orderedComplexBasepointSubcomplex M b) A}
    (H : SSet.RelativeMorphism.Homotopy
      (0 : NativeRelativeMorphism
        (orderedComplexBasepointSubcomplex M b) A) f) :
    orderedComplexSSet (simplicialCone M) ⊗ Δ[0] ⟶ underlyingSSet A :=
  extendedTerminalMap (literalConeBoundarySubcomplex M b).ι
    (underlyingSSet A)
    (tensorDeltaZeroMap
      (0 : orderedComplexSSet (simplicialCone M) ⟶ underlyingSSet A))
    (nativeNullhomotopyBoundaryPath M b A H)
    (nativeNullhomotopyBoundaryPath_initial M b A H)

omit [Fintype V] in
theorem nativeNullhomotopyExtendedTerminalMap_boundary
    (M : AbstractSimplicialComplex V) (b : V)
    (A : SimplicialObject AddCommGrpCat.{u})
    {f : NativeRelativeMorphism
      (orderedComplexBasepointSubcomplex M b) A}
    (H : SSet.RelativeMorphism.Homotopy
      (0 : NativeRelativeMorphism
        (orderedComplexBasepointSubcomplex M b) A) f) :
    (literalConeBoundarySubcomplex M b).ι ▷ Δ[0] ≫
        nativeNullhomotopyExtendedTerminalMap M b A H =
      (literalConeBoundarySubcomplex M b : SSet) ◁
          SSet.stdSimplex.δ (0 : Fin 2) ≫
        nativeNullhomotopyBoundaryPath M b A H := by
  exact extendedTerminalMap_restricts
    (literalConeBoundarySubcomplex M b).ι (underlyingSSet A)
    (tensorDeltaZeroMap
      (0 : orderedComplexSSet (simplicialCone M) ⟶ underlyingSSet A))
    (nativeNullhomotopyBoundaryPath M b A H)
    (nativeNullhomotopyBoundaryPath_initial M b A H)

omit [Fintype V] in
theorem nativeNullhomotopyExtendedTerminalMap_bottom
    (M : AbstractSimplicialComplex V) (b : V)
    (A : SimplicialObject AddCommGrpCat.{u})
    {f : NativeRelativeMorphism
      (orderedComplexBasepointSubcomplex M b) A}
    (H : SSet.RelativeMorphism.Homotopy
      (0 : NativeRelativeMorphism
        (orderedComplexBasepointSubcomplex M b) A) f) :
    literalConeBottomMap M ▷ Δ[0] ≫
        nativeNullhomotopyExtendedTerminalMap M b A H =
      tensorDeltaZeroMap f.map := by
  let j := SSet.Subcomplex.homOfLE
    (show literalConeBottomRange M ≤ literalConeBoundarySubcomplex M b
      from le_sup_left)
  have hfactor := congrArg (fun k ↦ k ▷ Δ[0])
    (literalConeBottomMap_factor_boundary M b)
  have hex :
      j ▷ Δ[0] ≫
          (literalConeBoundarySubcomplex M b : SSet) ◁
            SSet.stdSimplex.δ (0 : Fin 2) =
        (literalConeBottomRange M : SSet) ◁
            SSet.stdSimplex.δ (0 : Fin 2) ≫ j ▷ Δ[1] :=
    whisker_exchange j (SSet.stdSimplex.δ (0 : Fin 2))
  calc
    literalConeBottomMap M ▷ Δ[0] ≫
          nativeNullhomotopyExtendedTerminalMap M b A H =
        (SSet.Subcomplex.toRange (literalConeBottomMap M) ▷ Δ[0]) ≫
          (j ▷ Δ[0]) ≫
          ((literalConeBoundarySubcomplex M b).ι ▷ Δ[0]) ≫
          nativeNullhomotopyExtendedTerminalMap M b A H := by
      rw [← hfactor]
      simp only [comp_whiskerRight, Category.assoc, j]
    _ = (SSet.Subcomplex.toRange (literalConeBottomMap M) ▷ Δ[0]) ≫
          (j ▷ Δ[0]) ≫
          ((literalConeBoundarySubcomplex M b : SSet) ◁
            SSet.stdSimplex.δ (0 : Fin 2)) ≫
          nativeNullhomotopyBoundaryPath M b A H := by
      rw [nativeNullhomotopyExtendedTerminalMap_boundary]
    _ = (SSet.Subcomplex.toRange (literalConeBottomMap M) ▷ Δ[0]) ≫
          ((literalConeBottomRange M : SSet) ◁
            SSet.stdSimplex.δ (0 : Fin 2)) ≫
          (j ▷ Δ[1]) ≫
          nativeNullhomotopyBoundaryPath M b A H := by
      rw [← Category.assoc (j ▷ Δ[0])
        ((literalConeBoundarySubcomplex M b : SSet) ◁
          SSet.stdSimplex.δ (0 : Fin 2))
        (nativeNullhomotopyBoundaryPath M b A H), hex]
      simp only [Category.assoc]
    _ = boundaryTensorDeltaZeroMap f.map := by
      exact literalConeBoundaryHomotopy_hep_terminal_bottom M b A H.h
        (nativeNullhomotopy_rel_eq_zero M b A H) f.map H.h₁
    _ = tensorDeltaZeroMap f.map := rfl

omit [Fintype V] in
theorem nativeNullhomotopyExtendedTerminalMap_baseLine
    (M : AbstractSimplicialComplex V) (b : V)
    (A : SimplicialObject AddCommGrpCat.{u})
    {f : NativeRelativeMorphism
      (orderedComplexBasepointSubcomplex M b) A}
    (H : SSet.RelativeMorphism.Homotopy
      (0 : NativeRelativeMorphism
        (orderedComplexBasepointSubcomplex M b) A) f) :
    literalConeBaseLineMap M b ▷ Δ[0] ≫
        nativeNullhomotopyExtendedTerminalMap M b A H = 0 := by
  let j := SSet.Subcomplex.homOfLE
    (show literalConeBaseLineRange M b ≤ literalConeBoundarySubcomplex M b
      from le_sup_right)
  have hfactor := congrArg (fun k ↦ k ▷ Δ[0])
    (literalConeBaseLineMap_factor_boundary M b)
  have hex :
      j ▷ Δ[0] ≫
          (literalConeBoundarySubcomplex M b : SSet) ◁
            SSet.stdSimplex.δ (0 : Fin 2) =
        (literalConeBaseLineRange M b : SSet) ◁
            SSet.stdSimplex.δ (0 : Fin 2) ≫ j ▷ Δ[1] :=
    whisker_exchange j (SSet.stdSimplex.δ (0 : Fin 2))
  calc
    literalConeBaseLineMap M b ▷ Δ[0] ≫
          nativeNullhomotopyExtendedTerminalMap M b A H =
        (SSet.Subcomplex.toRange (literalConeBaseLineMap M b) ▷ Δ[0]) ≫
          (j ▷ Δ[0]) ≫
          ((literalConeBoundarySubcomplex M b).ι ▷ Δ[0]) ≫
          nativeNullhomotopyExtendedTerminalMap M b A H := by
      rw [← hfactor]
      simp only [comp_whiskerRight, Category.assoc, j]
    _ = (SSet.Subcomplex.toRange (literalConeBaseLineMap M b) ▷ Δ[0]) ≫
          (j ▷ Δ[0]) ≫
          ((literalConeBoundarySubcomplex M b : SSet) ◁
            SSet.stdSimplex.δ (0 : Fin 2)) ≫
          nativeNullhomotopyBoundaryPath M b A H := by
      rw [nativeNullhomotopyExtendedTerminalMap_boundary]
    _ = (SSet.Subcomplex.toRange (literalConeBaseLineMap M b) ▷ Δ[0]) ≫
          ((literalConeBaseLineRange M b : SSet) ◁
            SSet.stdSimplex.δ (0 : Fin 2)) ≫
          (j ▷ Δ[1]) ≫
          nativeNullhomotopyBoundaryPath M b A H := by
      rw [← Category.assoc (j ▷ Δ[0])
        ((literalConeBoundarySubcomplex M b : SSet) ◁
          SSet.stdSimplex.δ (0 : Fin 2))
        (nativeNullhomotopyBoundaryPath M b A H), hex]
      simp only [Category.assoc]
    _ = 0 := literalConeBoundaryHomotopy_hep_terminal_baseLine M b A H.h
      (nativeNullhomotopy_rel_eq_zero M b A H)

/-- A native relative nullhomotopy therefore produces the required strict
extension over the actual `Option` cone. -/
noncomputable def literalPointedExtensionOfNativeNullhomotopy
    (M : AbstractSimplicialComplex V) (b : V)
    (A : SimplicialObject AddCommGrpCat.{u})
    {f : NativeRelativeMorphism
      (orderedComplexBasepointSubcomplex M b) A}
    (H : SSet.RelativeMorphism.Homotopy
      (0 : NativeRelativeMorphism
        (orderedComplexBasepointSubcomplex M b) A) f) :
    LiteralPointedExtension M b A f :=
  literalPointedExtensionOfTensorDeltaZeroMap M b A f
    (nativeNullhomotopyExtendedTerminalMap M b A H)
    (nativeNullhomotopyExtendedTerminalMap_bottom M b A H)
    (nativeNullhomotopyExtendedTerminalMap_baseLine M b A H)

omit [Fintype V] in
/-- Class-zero native pointed maps admit literal pointed extensions. -/
theorem nonempty_literalPointedExtension_of_mem_nativeNullMaps
    (M : AbstractSimplicialComplex V) (b : V)
    (A : SimplicialObject AddCommGrpCat.{u})
    (f : NativeRelativeMorphism
      (orderedComplexBasepointSubcomplex M b) A)
    (hf : f ∈ NativeNullMaps
      (orderedComplexBasepointSubcomplex M b) A) :
    Nonempty (LiteralPointedExtension M b A f) := by
  have hfzero : f.homotopyClass = 0 :=
    LinearMap.mem_ker.mp hf
  have hzero :
      (0 : NativeRelativeMorphism
        (orderedComplexBasepointSubcomplex M b) A).homotopyClass = 0 :=
    homotopyClass_zero (orderedComplexBasepointSubcomplex M b) A
  have hclass :
      (0 : NativeRelativeMorphism
        (orderedComplexBasepointSubcomplex M b) A).homotopyClass =
        f.homotopyClass := hzero.trans hfzero.symm
  rcases (homotopyClass_eq_iff
    (orderedComplexBasepointSubcomplex M b) A).mp hclass with ⟨H⟩
  exact ⟨literalPointedExtensionOfNativeNullhomotopy M b A H⟩

end GeneralSphereT.SimplicialCochain
