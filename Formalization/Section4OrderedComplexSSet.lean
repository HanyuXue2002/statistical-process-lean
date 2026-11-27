import Formalization.Section4RelativeMappingGroups
import Formalization.FiniteSimplicialCochain
import Formalization.SimplicialCochainPullback
import Mathlib.AlgebraicTopology.SimplicialSet.NerveNondegenerate

set_option linter.style.header false

/-!
# Section 4: the simplicial set of an ordered simplicial complex

The finite-complex part of the proof uses nondegenerate oriented simplices,
whereas Mathlib's homotopy API uses honest simplicial sets.  This file gives
the standard bridge.  An `n`-simplex is a monotone (not necessarily
injective) vertex string whose finite image is a face of the complex;
precomposition supplies all faces and degeneracies.

The construction is also functorial for the ordered simplicial embeddings
used throughout the formalization.  Thus the source objects in the native
relative-homotopy layer are no longer abstract placeholders.
-/

noncomputable section

open CategoryTheory CategoryTheory.Category Opposite Simplicial

namespace GeneralSphereT.SimplicialCochain

universe u

variable {V : Type u} [LinearOrder V]

/-- The finite support of a possibly degenerate ordered simplex. -/
def orderedSimplexSupport {n : ℕ}
    (x : Fin (n + 1) →o V) : Finset V :=
  Finset.univ.image x

@[simp]
theorem mem_orderedSimplexSupport {n : ℕ}
    (x : Fin (n + 1) →o V) (v : V) :
    v ∈ orderedSimplexSupport x ↔ ∃ i, x i = v := by
  simp [orderedSimplexSupport]

/-- Precomposition can only decrease the support of an ordered simplex. -/
theorem orderedSimplexSupport_comp_subset
    {m n : ℕ} (x : Fin (n + 1) →o V)
    (f : Fin (m + 1) →o Fin (n + 1)) :
    orderedSimplexSupport (x.comp f) ⊆ orderedSimplexSupport x := by
  intro v hv
  rw [mem_orderedSimplexSupport] at hv ⊢
  rcases hv with ⟨i, rfl⟩
  exact ⟨f i, rfl⟩

/-- The honest simplicial set associated with a finite ordered abstract
simplicial complex.  Degenerate simplices are retained. -/
def orderedComplexSSet (M : AbstractSimplicialComplex V) : SSet.{u} where
  obj Δ :=
    {x : Fin (Δ.unop.len + 1) →o V // orderedSimplexSupport x ∈ M}
  map {Δ Δ'} θ := ↾fun x ↦
    ⟨x.1.comp θ.unop.toOrderHom, by
      apply (M.isRelLowerSet_faces x.2).2
      · exact orderedSimplexSupport_comp_subset x.1 θ.unop.toOrderHom
      · exact Finset.image_nonempty.mpr Finset.univ_nonempty⟩
  map_id Δ := by
    ext x i
    rfl
  map_comp θ φ := by
    ext x i
    rfl

@[simp]
theorem orderedComplexSSet_map_coe
    (M : AbstractSimplicialComplex V)
    {Δ Δ' : SimplexCategoryᵒᵖ} (θ : Δ ⟶ Δ')
    (x : (orderedComplexSSet M).obj Δ) :
    ((orderedComplexSSet M).map θ x).1 =
      x.1.comp θ.unop.toOrderHom :=
  rfl

/-! ## Nondegenerate simplices -/

/-- Forgetting the face condition embeds the simplicial set of a complex in
the nerve of its ordered vertex set. -/
def orderedComplexSSetToNerve (M : AbstractSimplicialComplex V) :
    orderedComplexSSet M ⟶ nerve V where
  app Δ := ↾fun x ↦ x.1.monotone.functor
  naturality Δ Δ' θ := by
    ext x i
    rfl

instance orderedComplexSSetToNerve_mono
    (M : AbstractSimplicialComplex V) :
    Mono (orderedComplexSSetToNerve M) := by
  rw [NatTrans.mono_iff_mono_app]
  intro Δ
  rw [mono_iff_injective]
  intro x y h
  apply Subtype.ext
  ext i
  exact Functor.congr_obj h i

/-- A simplex of the ordered-complex simplicial set is nondegenerate exactly
when its vertex string is injective (equivalently, strictly increasing). -/
theorem mem_orderedComplexSSet_nonDegenerate_iff_injective
    (M : AbstractSimplicialComplex V) {n : ℕ}
    (x : (orderedComplexSSet M) _⦋n⦌) :
    x ∈ (orderedComplexSSet M).nonDegenerate n ↔
      Function.Injective x.1 := by
  rw [← SSet.nonDegenerate_iff_of_mono (orderedComplexSSetToNerve M)]
  exact PartialOrder.mem_nerve_nonDegenerate_iff_injective _

/-- The nondegenerate simplices in the honest simplicial set are exactly the
oriented simplices used by the finite ordered cochain model. -/
def nonDegenerateSimplexEquiv (M : AbstractSimplicialComplex V) (n : ℕ) :
    (orderedComplexSSet M).nonDegenerate n ≃ Simplex M n where
  toFun x :=
    ⟨orderedSimplexSupport x.1.1, x.1.2,
      by
        rw [orderedSimplexSupport,
          Finset.card_image_of_injective Finset.univ
            ((mem_orderedComplexSSet_nonDegenerate_iff_injective M x.1).1 x.2)]
        simp⟩
  invFun s :=
    ⟨⟨(s.1.orderEmbOfFin s.2.2).toOrderHom,
        by simpa [orderedSimplexSupport] using s.2.1⟩,
      (mem_orderedComplexSSet_nonDegenerate_iff_injective M _).2
        (s.1.orderEmbOfFin s.2.2).injective⟩
  left_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    apply OrderHom.ext
    funext i
    have hxinj : Function.Injective x.1.1 :=
      (mem_orderedComplexSSet_nonDegenerate_iff_injective M x.1).1 x.2
    have hxmem : ∀ i, x.1.1 i ∈ orderedSimplexSupport x.1.1 := by
      intro j
      exact (mem_orderedSimplexSupport x.1.1 (x.1.1 j)).2 ⟨j, rfl⟩
    exact congrFun
      (Finset.orderEmbOfFin_unique
        (by
          rw [orderedSimplexSupport,
            Finset.card_image_of_injective Finset.univ hxinj]
          simp)
        hxmem (x.1.1.monotone.strictMono_of_injective hxinj)).symm i
  right_inv s := by
    apply Subtype.ext
    simp [orderedSimplexSupport]

/-- A vertex as a zero-simplex of the associated simplicial set. -/
def orderedComplexVertex (M : AbstractSimplicialComplex V) (v : V) :
    (orderedComplexSSet M).obj
      (Opposite.op (SimplexCategory.mk 0)) := by
  refine ⟨OrderHom.const _ v, ?_⟩
  change orderedSimplexSupport (OrderHom.const (Fin 1) v) ∈ M.faces
  have hs : orderedSimplexSupport (OrderHom.const (Fin 1) v) = {v} := by
    ext w
    simp [orderedSimplexSupport]
  rw [hs]
  exact M.singleton_mem v

@[simp]
theorem orderedComplexVertex_apply
    (M : AbstractSimplicialComplex V) (v : V) (i : Fin 1) :
    (orderedComplexVertex M v).1 i = v :=
  rfl

/-- The simplicial subcomplex generated by the chosen basepoint.  Its
simplices are precisely the degeneracies of that vertex, so relative maps
which vanish on it are genuine pointed maps. -/
def orderedComplexBasepointSubcomplex
    (M : AbstractSimplicialComplex V) (b : V) :
    (orderedComplexSSet M).Subcomplex :=
  SSet.Subcomplex.ofSimplex (orderedComplexVertex M b)

/-! ## Functoriality for the embeddings used by the cochain model -/

variable {W : Type u} [LinearOrder W]
variable {M : AbstractSimplicialComplex V}
variable {N : AbstractSimplicialComplex W}

/-- Postcomposition of an ordered simplex with an order embedding has the
expected finite support. -/
theorem orderedSimplexSupport_postcomp_embedding
    (e : V ↪o W) {n : ℕ} (x : Fin (n + 1) →o V) :
    orderedSimplexSupport (e.toOrderHom.comp x) =
      (orderedSimplexSupport x).map e.toEmbedding := by
  ext w
  simp [orderedSimplexSupport]

/-- An ordered simplicial embedding induces a genuine map of simplicial
sets, including all degenerate simplices. -/
def OrderedSimplicialMap.toSSetMap (F : OrderedSimplicialMap M N) :
    orderedComplexSSet M ⟶ orderedComplexSSet N where
  app Δ := ↾fun x ↦
    ⟨F.toOrderEmbedding.toOrderHom.comp x.1, by
      rw [orderedSimplexSupport_postcomp_embedding]
      exact F.map_mem x.2⟩
  naturality Δ Δ' θ := by
    ext x
    rfl

@[simp]
theorem OrderedSimplicialMap.toSSetMap_app_coe
    (F : OrderedSimplicialMap M N)
    (Δ : SimplexCategoryᵒᵖ) (x : (orderedComplexSSet M).obj Δ) :
    (F.toSSetMap.app Δ x).1 =
      F.toOrderEmbedding.toOrderHom.comp x.1 :=
  rfl

@[simp]
theorem OrderedSimplicialMap.toSSetMap_vertex
    (F : OrderedSimplicialMap M N) (v : V) :
    F.toSSetMap.app (Opposite.op (SimplexCategory.mk 0))
        (orderedComplexVertex M v) =
      orderedComplexVertex N (F.toOrderEmbedding v) := by
  apply Subtype.ext
  ext i
  fin_cases i
  rfl

end GeneralSphereT.SimplicialCochain
