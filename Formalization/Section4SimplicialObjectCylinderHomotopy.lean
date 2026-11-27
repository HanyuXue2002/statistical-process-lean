import Formalization.Section4NativeRelativeHomotopyGroup
import Mathlib.AlgebraicTopology.SimplexCategory.MorphismProperty
import Mathlib.AlgebraicTopology.SimplicialSet.Homotopy

set_option linter.style.header false

/-!
# Section 4: combinatorial homotopies as cylinder homotopies

Mathlib currently provides the map from a simplicial-set cylinder homotopy
to a combinatorial `SimplicialObject.Homotopy`, but not the converse.  This
file constructs the converse.  An `n`-simplex of `Δ[1]` is indexed by the
number of its initial zeroes.  At the cut indexed by `k`, the cylinder map is
the `k`-th face of the adjacent prism operator supplied by the combinatorial
homotopy.
-/

noncomputable section

open CategoryTheory CategoryTheory.Category Opposite Simplicial
open MonoidalCategory CartesianMonoidalCategory

namespace GeneralSphereT.Section4
namespace SimplicialObjectCylinderHomotopy

universe u

variable {X Y : SSet.{u}} {f g : X ⟶ Y}

/-- The standard indexing of the simplices of `Δ[1]` by the number of
initial zeroes. -/
def intervalSimplexEquiv (n : ℕ) :
    Fin (n + 2) ≃ Δ[1].obj (op ⦋n⦌) :=
  Equiv.ofBijective SSet.stdSimplex.objMk₁
    SSet.stdSimplex.objMk₁_bijective

@[simp]
theorem intervalSimplexEquiv_apply {n : ℕ} (k : Fin (n + 2)) :
    intervalSimplexEquiv n k = SSet.stdSimplex.objMk₁ k :=
  rfl

@[simp]
theorem intervalSimplexEquiv_symm_objMk₁ {n : ℕ} (k : Fin (n + 2)) :
    (intervalSimplexEquiv n).symm (SSet.stdSimplex.objMk₁ k) = k :=
  (intervalSimplexEquiv n).symm_apply_apply k

/-- The prism operator adjacent to a cut.  At the all-one simplex we use
the first operator; otherwise we use the predecessor of the cut. -/
def prismIndex {n : ℕ} (k : Fin (n + 2)) : Fin (n + 1) :=
  if hk : k = 0 then 0 else k.pred hk

@[simp]
theorem prismIndex_zero {n : ℕ} :
    prismIndex (0 : Fin (n + 2)) = 0 := by
  simp [prismIndex]

@[simp]
theorem prismIndex_succ {n : ℕ} (i : Fin (n + 1)) :
    prismIndex i.succ = i := by
  simp [prismIndex]

/-- The degree-`n` component reconstructed from a combinatorial homotopy. -/
def cylinderApp
    (H : SimplicialObject.Homotopy f g) (n : ℕ) :
    (X ⊗ Δ[1]).obj (op ⦋n⦌) ⟶ Y.obj (op ⦋n⦌) :=
  ↾fun z ↦
    let k := (intervalSimplexEquiv n).symm z.2
    (H.h (prismIndex k) ≫ Y.δ k).hom z.1

@[simp]
theorem cylinderApp_apply_objMk₁
    (H : SimplicialObject.Homotopy f g) {n : ℕ}
    (x : X.obj (op ⦋n⦌)) (k : Fin (n + 2)) :
    (cylinderApp H n).hom
        (x, SSet.stdSimplex.objMk₁ k) =
      (H.h (prismIndex k) ≫ Y.δ k).hom x := by
  change
    (H.h (prismIndex ((intervalSimplexEquiv n).symm
        (SSet.stdSimplex.objMk₁ k))) ≫
      Y.δ ((intervalSimplexEquiv n).symm
        (SSet.stdSimplex.objMk₁ k))).hom x = _
  rw [intervalSimplexEquiv_symm_objMk₁]

/-- Compatibility of the reconstructed components with a face map. -/
theorem cylinderApp_naturality_δ
    (H : SimplicialObject.Homotopy f g) {n : ℕ}
    (j : Fin (n + 2)) :
    (X ⊗ Δ[1]).δ j ≫ cylinderApp H n =
      cylinderApp H (n + 1) ≫ Y.δ j := by
  ext z
  rcases z with ⟨x, t⟩
  obtain ⟨k, rfl⟩ := SSet.stdSimplex.objMk₁_surjective t
  change (cylinderApp H n).hom
      ((X.δ j).hom x, (Δ[1].δ j).hom
        (SSet.stdSimplex.objMk₁ k)) =
    (Y.δ j).hom ((cylinderApp H (n + 1)).hom
      (x, SSet.stdSimplex.objMk₁ k))
  by_cases hkj : k ≤ j.castSucc
  · rw [SSet.stdSimplex.δ_objMk₁_of_le k j hkj]
    rw [cylinderApp_apply_objMk₁, cylinderApp_apply_objMk₁]
    rcases Fin.eq_zero_or_eq_succ k with rfl | ⟨i, rfl⟩
    · change
        ((H.h 0 ≫ Y.δ 0).hom ((X.δ j).hom x)) =
          (Y.δ j).hom ((H.h 0 ≫ Y.δ 0).hom x)
      rw [H.h_zero_comp_δ_zero, H.h_zero_comp_δ_zero]
      exact ConcreteCategory.congr_hom
        (SimplicialObject.δ_naturality g j) x
    · have hi : i ≠ Fin.last (n + 1) := by
        intro hi
        subst i
        simp at hkj
      obtain ⟨p, rfl⟩ := Fin.eq_castSucc_of_ne_last hi
      have hpj : p.castSucc < j := by grind
      change
        ((X.δ j ≫ H.h p ≫ Y.δ p.succ).hom x) =
          ((H.h p.castSucc ≫ Y.δ p.castSucc.succ ≫ Y.δ j).hom x)
      apply ConcreteCategory.congr_hom
      have hface :
          Y.δ p.castSucc.succ ≫ Y.δ j =
            Y.δ j.succ ≫ Y.δ p.succ := by
        simpa only [Fin.succ_castSucc] using
          (Y.δ_comp_δ (i := p.succ) (j := j)
            (by grind)).symm
      calc
        X.δ j ≫ H.h p ≫ Y.δ p.succ =
            (X.δ j ≫ H.h p) ≫ Y.δ p.succ :=
          (Category.assoc _ _ _).symm
        _ = (H.h p.castSucc ≫ Y.δ j.succ) ≫ Y.δ p.succ := by
          rw [H.h_castSucc_comp_δ_succ_of_lt j p hpj]
        _ = H.h p.castSucc ≫
            (Y.δ j.succ ≫ Y.δ p.succ) := Category.assoc _ _ _
        _ = H.h p.castSucc ≫
            (Y.δ p.castSucc.succ ≫ Y.δ j) := by rw [hface]
        _ = H.h p.castSucc ≫ Y.δ p.castSucc.succ ≫ Y.δ j :=
          (Category.assoc _ _ _).symm
  · rw [not_le] at hkj
    rw [SSet.stdSimplex.δ_objMk₁_of_lt k j hkj]
    rw [cylinderApp_apply_objMk₁, cylinderApp_apply_objMk₁]
    obtain ⟨i, rfl⟩ := Fin.eq_succ_of_ne_zero (by grind : k ≠ 0)
    by_cases hi : i = Fin.last (n + 1)
    · subst i
      change
        ((H.h (Fin.last n) ≫ Y.δ (Fin.last (n + 1))).hom
            ((X.δ j).hom x)) =
          (Y.δ j).hom
            ((H.h (Fin.last (n + 1)) ≫
              Y.δ (Fin.last (n + 2))).hom x)
      rw [H.h_last_comp_δ_last, H.h_last_comp_δ_last]
      exact ConcreteCategory.congr_hom
        (SimplicialObject.δ_naturality f j) x
    · obtain ⟨p, rfl⟩ := Fin.eq_castSucc_of_ne_last hi
      rcases Fin.eq_zero_or_eq_succ p with rfl | ⟨q, rfl⟩
      · have hj : j = 0 := by
          apply Fin.ext
          grind
        subst j
        change
          ((X.δ 0 ≫ H.h 0 ≫ Y.δ 0).hom x) =
            ((H.h 0 ≫ Y.δ 1 ≫ Y.δ 0).hom x)
        apply ConcreteCategory.congr_hom
        have hface : Y.δ (1 : Fin (n + 3)) ≫ Y.δ 0 =
            Y.δ 0 ≫ Y.δ 0 := by
          simpa using Y.δ_comp_δ (i := (0 : Fin (n + 2)))
            (j := (0 : Fin (n + 2))) (Fin.zero_le _)
        calc
          X.δ 0 ≫ H.h 0 ≫ Y.δ 0 =
              X.δ 0 ≫ g.app (op ⦋n⦌) := by
            rw [H.h_zero_comp_δ_zero]
          _ = g.app (op ⦋n + 1⦌) ≫ Y.δ 0 :=
            SimplicialObject.δ_naturality g 0
          _ = (H.h 0 ≫ Y.δ 0) ≫ Y.δ 0 := by
            rw [H.h_zero_comp_δ_zero]
          _ = H.h 0 ≫ (Y.δ 0 ≫ Y.δ 0) := Category.assoc _ _ _
          _ = H.h 0 ≫ (Y.δ 1 ≫ Y.δ 0) := by rw [hface]
          _ = H.h 0 ≫ Y.δ 1 ≫ Y.δ 0 :=
            (Category.assoc _ _ _).symm
      · by_cases hj : j = q.succ.castSucc
        · subst j
          change
            ((X.δ q.succ.castSucc ≫ H.h q.castSucc ≫
                Y.δ q.succ.castSucc).hom x) =
              ((H.h q.castSucc.succ ≫
                Y.δ q.succ.castSucc.succ ≫
                Y.δ q.succ.castSucc).hom x)
          apply ConcreteCategory.congr_hom
          have hface :
              Y.δ q.succ.castSucc.succ ≫ Y.δ q.succ.castSucc =
                Y.δ q.succ.castSucc.castSucc ≫
                  Y.δ q.succ.castSucc := by
            simpa only [Fin.succ_castSucc] using
              Y.δ_comp_δ (i := q.succ.castSucc)
                (j := q.succ.castSucc) (le_rfl)
          have hmiddle :
              H.h q.castSucc.succ ≫
                  Y.δ q.succ.castSucc.castSucc =
                H.h q.castSucc.castSucc ≫
                  Y.δ q.succ.castSucc.castSucc := by
            simpa only [Fin.succ_castSucc] using
              H.h_succ_comp_δ_castSucc_succ q.castSucc
          have hface' :
              Y.δ q.succ.castSucc.castSucc ≫
                  Y.δ q.succ.castSucc =
                Y.δ q.succ.castSucc.succ ≫
                  Y.δ q.succ.castSucc := by
            simpa only [Fin.succ_castSucc] using
              (Y.δ_comp_δ (i := q.succ.castSucc)
                (j := q.succ.castSucc) (le_rfl)).symm
          have hhom :
              H.h q.castSucc.castSucc ≫
                  Y.δ q.succ.castSucc.succ =
                X.δ q.succ.castSucc ≫ H.h q.castSucc := by
            exact H.h_castSucc_comp_δ_succ_of_lt
              q.succ.castSucc q.castSucc (by grind)
          calc
            X.δ q.succ.castSucc ≫ H.h q.castSucc ≫
                Y.δ q.succ.castSucc =
              (X.δ q.succ.castSucc ≫ H.h q.castSucc) ≫
                Y.δ q.succ.castSucc :=
                  (Category.assoc _ _ _).symm
            _ = (H.h q.castSucc.castSucc ≫
                Y.δ q.succ.castSucc.succ) ≫
                Y.δ q.succ.castSucc := by rw [hhom]
            _ = H.h q.castSucc.castSucc ≫
                (Y.δ q.succ.castSucc.succ ≫
                  Y.δ q.succ.castSucc) :=
                  Category.assoc _ _ _
            _ = H.h q.castSucc.castSucc ≫
                (Y.δ q.succ.castSucc.castSucc ≫
                  Y.δ q.succ.castSucc) := by rw [hface']
            _ = (H.h q.castSucc.castSucc ≫
                Y.δ q.succ.castSucc.castSucc) ≫
                  Y.δ q.succ.castSucc :=
                    (Category.assoc _ _ _).symm
            _ = (H.h q.castSucc.succ ≫
                Y.δ q.succ.castSucc.castSucc) ≫
                  Y.δ q.succ.castSucc := by rw [hmiddle]
            _ = H.h q.castSucc.succ ≫
                (Y.δ q.succ.castSucc.castSucc ≫
                  Y.δ q.succ.castSucc) := Category.assoc _ _ _
            _ = H.h q.castSucc.succ ≫
                (Y.δ q.succ.castSucc.succ ≫
                  Y.δ q.succ.castSucc) := by rw [hface]
            _ = H.h q.castSucc.succ ≫
                Y.δ q.succ.castSucc.succ ≫
                  Y.δ q.succ.castSucc :=
                    (Category.assoc _ _ _).symm
        · have hjlt : j < q.succ.castSucc := by grind
          change
            ((X.δ j ≫ H.h q.castSucc ≫
                Y.δ q.succ.castSucc).hom x) =
              ((H.h q.castSucc.succ ≫
                Y.δ q.succ.castSucc.succ ≫ Y.δ j).hom x)
          apply ConcreteCategory.congr_hom
          have hface :
              Y.δ q.succ.castSucc.succ ≫ Y.δ j =
                Y.δ j.castSucc ≫ Y.δ q.succ.castSucc := by
            simpa only [Fin.succ_castSucc] using
              Y.δ_comp_δ (i := j) (j := q.succ.castSucc)
                (by grind)
          have hhom :
              H.h q.castSucc.succ ≫ Y.δ j.castSucc =
                X.δ j ≫ H.h q.castSucc :=
            H.h_succ_comp_δ_castSucc_of_lt j q.castSucc (by grind)
          calc
            X.δ j ≫ H.h q.castSucc ≫ Y.δ q.succ.castSucc =
                (X.δ j ≫ H.h q.castSucc) ≫
                  Y.δ q.succ.castSucc :=
                    (Category.assoc _ _ _).symm
            _ = (H.h q.castSucc.succ ≫ Y.δ j.castSucc) ≫
                  Y.δ q.succ.castSucc := by rw [hhom]
            _ = H.h q.castSucc.succ ≫
                (Y.δ j.castSucc ≫ Y.δ q.succ.castSucc) :=
                  Category.assoc _ _ _
            _ = H.h q.castSucc.succ ≫
                (Y.δ q.succ.castSucc.succ ≫ Y.δ j) := by rw [hface]
            _ = H.h q.castSucc.succ ≫
                Y.δ q.succ.castSucc.succ ≫ Y.δ j :=
                  (Category.assoc _ _ _).symm

/-- Compatibility of the reconstructed components with a degeneracy map. -/
theorem cylinderApp_naturality_σ
    (H : SimplicialObject.Homotopy f g) {n : ℕ}
    (j : Fin (n + 1)) :
    (X ⊗ Δ[1]).σ j ≫ cylinderApp H (n + 1) =
      cylinderApp H n ≫ Y.σ j := by
  ext z
  rcases z with ⟨x, t⟩
  obtain ⟨k, rfl⟩ := SSet.stdSimplex.objMk₁_surjective t
  change (cylinderApp H (n + 1)).hom
      ((X.σ j).hom x, (Δ[1].σ j).hom
        (SSet.stdSimplex.objMk₁ k)) =
    (Y.σ j).hom ((cylinderApp H n).hom
      (x, SSet.stdSimplex.objMk₁ k))
  by_cases hkj : k ≤ j.castSucc
  · rw [SSet.stdSimplex.σ_objMk₁_of_le k j hkj]
    rw [cylinderApp_apply_objMk₁, cylinderApp_apply_objMk₁]
    rcases Fin.eq_zero_or_eq_succ k with rfl | ⟨i, rfl⟩
    · change
        ((H.h 0 ≫ Y.δ 0).hom ((X.σ j).hom x)) =
          (Y.σ j).hom ((H.h 0 ≫ Y.δ 0).hom x)
      rw [H.h_zero_comp_δ_zero, H.h_zero_comp_δ_zero]
      exact ConcreteCategory.congr_hom
        (SimplicialObject.σ_naturality g j) x
    · have hij : i ≤ j := by grind
      change
        ((X.σ j ≫ H.h i.castSucc ≫
            Y.δ i.succ.castSucc).hom x) =
          ((H.h i ≫ Y.δ i.succ ≫ Y.σ j).hom x)
      apply ConcreteCategory.congr_hom
      have hhom :
          H.h i ≫ Y.σ j.succ = X.σ j ≫ H.h i.castSucc :=
        H.h_comp_σ_succ_of_lt j i hij
      have hface :
          Y.σ j.succ ≫ Y.δ i.succ.castSucc =
            Y.δ i.succ ≫ Y.σ j :=
        Y.δ_comp_σ_of_le (i := i.succ) (j := j) hkj
      calc
        X.σ j ≫ H.h i.castSucc ≫ Y.δ i.succ.castSucc =
            (X.σ j ≫ H.h i.castSucc) ≫
              Y.δ i.succ.castSucc :=
                (Category.assoc _ _ _).symm
        _ = (H.h i ≫ Y.σ j.succ) ≫
              Y.δ i.succ.castSucc := by rw [hhom]
        _ = H.h i ≫ (Y.σ j.succ ≫
              Y.δ i.succ.castSucc) := Category.assoc _ _ _
        _ = H.h i ≫ (Y.δ i.succ ≫ Y.σ j) := by rw [hface]
        _ = H.h i ≫ Y.δ i.succ ≫ Y.σ j :=
          (Category.assoc _ _ _).symm
  · rw [not_le] at hkj
    rw [SSet.stdSimplex.σ_objMk₁_of_lt k j hkj]
    rw [cylinderApp_apply_objMk₁, cylinderApp_apply_objMk₁]
    obtain ⟨i, rfl⟩ := Fin.eq_succ_of_ne_zero (by grind : k ≠ 0)
    have hji : j ≤ i := by grind
    change
      ((X.σ j ≫ H.h i.succ ≫ Y.δ i.succ.succ).hom x) =
        ((H.h i ≫ Y.δ i.succ ≫ Y.σ j).hom x)
    apply ConcreteCategory.congr_hom
    have hhom :
        H.h i ≫ Y.σ j.castSucc = X.σ j ≫ H.h i.succ :=
      H.h_comp_σ_castSucc_of_le j i hji
    have hface :
        Y.σ j.castSucc ≫ Y.δ i.succ.succ =
          Y.δ i.succ ≫ Y.σ j :=
      Y.δ_comp_σ_of_gt (i := i.succ) (j := j) (by grind)
    calc
      X.σ j ≫ H.h i.succ ≫ Y.δ i.succ.succ =
          (X.σ j ≫ H.h i.succ) ≫ Y.δ i.succ.succ :=
            (Category.assoc _ _ _).symm
      _ = (H.h i ≫ Y.σ j.castSucc) ≫ Y.δ i.succ.succ := by
        rw [hhom]
      _ = H.h i ≫ (Y.σ j.castSucc ≫ Y.δ i.succ.succ) :=
        Category.assoc _ _ _
      _ = H.h i ≫ (Y.δ i.succ ≫ Y.σ j) := by rw [hface]
      _ = H.h i ≫ Y.δ i.succ ≫ Y.σ j :=
        (Category.assoc _ _ _).symm

/-- The reconstructed component at an arbitrary simplex-category object. -/
def cylinderAppObj
    (H : SimplicialObject.Homotopy f g) (Δ : SimplexCategory) :
    (X ⊗ Δ[1]).obj (op Δ) ⟶ Y.obj (op Δ) := by
  induction Δ using SimplexCategory.rec with
  | _ n => exact cylinderApp H n

@[simp]
theorem cylinderAppObj_mk
    (H : SimplicialObject.Homotopy f g) (n : ℕ) :
    cylinderAppObj H ⦋n⦌ = cylinderApp H n :=
  rfl

/-- Naturality of the reconstructed components for every simplex-category
morphism.  The simplex category is generated under composition by faces and
degeneracies, so the two calculations above suffice. -/
theorem cylinderAppObj_naturality
    (H : SimplicialObject.Homotopy f g)
    {Δ Δ' : SimplexCategory} (θ : Δ ⟶ Δ') :
    (X ⊗ Δ[1]).map θ.op ≫ cylinderAppObj H Δ =
      cylinderAppObj H Δ' ≫ Y.map θ.op := by
  let W : MorphismProperty SimplexCategory :=
    fun Δ Δ' θ ↦
      (X ⊗ Δ[1]).map θ.op ≫ cylinderAppObj H Δ =
        cylinderAppObj H Δ' ≫ Y.map θ.op
  let _ : W.IsMultiplicative := {
    id_mem Δ := by
      change (X ⊗ Δ[1]).map (𝟙 Δ).op ≫ cylinderAppObj H Δ =
        cylinderAppObj H Δ ≫ Y.map (𝟙 Δ).op
      rw [show (𝟙 Δ).op = 𝟙 (op Δ) by rfl,
        (X ⊗ Δ[1]).map_id, Y.map_id, Category.id_comp,
        Category.comp_id]
    comp_mem θ ψ hθ hψ := by
      change (X ⊗ Δ[1]).map θ.op ≫ cylinderAppObj H _ =
        cylinderAppObj H _ ≫ Y.map θ.op at hθ
      change (X ⊗ Δ[1]).map ψ.op ≫ cylinderAppObj H _ =
        cylinderAppObj H _ ≫ Y.map ψ.op at hψ
      change (X ⊗ Δ[1]).map (θ ≫ ψ).op ≫ cylinderAppObj H _ =
        cylinderAppObj H _ ≫ Y.map (θ ≫ ψ).op
      rw [show (θ ≫ ψ).op = ψ.op ≫ θ.op by rfl,
        (X ⊗ Δ[1]).map_comp, Y.map_comp]
      simp only [Category.assoc]
      rw [hθ, ← Category.assoc, hψ, Category.assoc] }
  have hδ : ∀ {n : ℕ} (i : Fin (n + 2)),
      W (SimplexCategory.δ i) := by
    intro n i
    simpa only [W, cylinderAppObj_mk, SimplicialObject.δ_def] using
      cylinderApp_naturality_δ H i
  have hσ : ∀ {n : ℕ} (i : Fin (n + 1)),
      W (SimplexCategory.σ i) := by
    intro n i
    simpa only [W, cylinderAppObj_mk, SimplicialObject.σ_def] using
      cylinderApp_naturality_σ H i
  have htop : W = ⊤ :=
    SimplexCategory.morphismProperty_eq_top W hδ hσ
  have hθ : W θ := by
    rw [htop]
    trivial
  exact hθ

/-- The actual simplicial-set cylinder map reconstructed from a
combinatorial homotopy. -/
def cylinderMap (H : SimplicialObject.Homotopy f g) :
    X ⊗ Δ[1] ⟶ Y where
  app Δ := cylinderAppObj H Δ.unop
  naturality Δ Δ' θ := by
    simpa using cylinderAppObj_naturality H θ.unop

/-- The `0` endpoint is the all-zero interval simplex. -/
theorem ι₀_app_eq_objMk₁_last {n : ℕ} (x : X.obj (op ⦋n⦌)) :
    SSet.ι₀.app (op ⦋n⦌) x =
      (x, SSet.stdSimplex.objMk₁ (Fin.last (n + 1))) := by
  apply Prod.ext
  · rfl
  · ext i
    simp [SSet.stdSimplex.objMk₁_apply,
      SSet.ι₀_app_snd_apply]

/-- The `1` endpoint is the all-one interval simplex. -/
theorem ι₁_app_eq_objMk₁_zero {n : ℕ} (x : X.obj (op ⦋n⦌)) :
    SSet.ι₁.app (op ⦋n⦌) x =
      (x, SSet.stdSimplex.objMk₁ 0) := by
  apply Prod.ext
  · rfl
  · ext i
    simp [SSet.stdSimplex.objMk₁_apply,
      SSet.ι₁_app_snd_apply]

/-- Converse to Mathlib's `SSet.Homotopy.toSimplicialObjectHomotopy`:
every combinatorial simplicial homotopy determines an actual cylinder
homotopy. -/
def toCylinderHomotopy
    (H : SimplicialObject.Homotopy f g) : SSet.Homotopy f g where
  h := cylinderMap H
  h₀ := by
    ext Δ x
    induction Δ using Opposite.rec with
    | _ Δ =>
      induction Δ using SimplexCategory.rec with
      | _ n =>
        change (cylinderApp H n).hom
            (SSet.ι₀.app (op ⦋n⦌) x) = f.app (op ⦋n⦌) x
        rw [ι₀_app_eq_objMk₁_last,
          cylinderApp_apply_objMk₁]
        change (H.h (Fin.last n) ≫
          Y.δ (Fin.last (n + 1))).hom x = _
        rw [H.h_last_comp_δ_last]
  h₁ := by
    ext Δ x
    induction Δ using Opposite.rec with
    | _ Δ =>
      induction Δ using SimplexCategory.rec with
      | _ n =>
        change (cylinderApp H n).hom
            (SSet.ι₁.app (op ⦋n⦌) x) = g.app (op ⦋n⦌) x
        rw [ι₁_app_eq_objMk₁_zero,
          cylinderApp_apply_objMk₁]
        change (H.h 0 ≫ Y.δ 0).hom x = _
        rw [H.h_zero_comp_δ_zero]
  rel := by
    ext Δ x
    exact False.elim (by simpa using x.1.property)

end SimplicialObjectCylinderHomotopy
end GeneralSphereT.Section4
