import Formalization.Section4DoldKanCochainBridge
import Formalization.Section4DoldKanProjection
import Formalization.FiniteSimplicialCochain
import Mathlib.Algebra.Category.Grp.Biproducts
import Mathlib.Order.Hom.PowersetCard

set_option linter.style.header false

/-!
# Section 4: finite coordinates for the explicit Dold--Kan bridge

This file isolates the finite combinatorics which is suppressed by the
categorical construction of `StandardModels.K` and `StandardModels.L`.
It proves that faces of the standard simplex are the same thing as increasing
injections between finite ordinals and, including all signs, identifies the
paper's coboundary with the alternating coface formula.

The file also constructs the canonical degreewise cut-point equivalence from
the epimorphism indices occurring in `Γ₀.Obj.obj₂` to anchored faces.  After
that reindexing, the disk model uses the signed coordinates consisting of
values on anchored `(q-1)`-faces and coboundary values on anchored `q`-faces.
The remaining issue beyond this file is simplicial naturality of this signed
basis under an arbitrary simplex map.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits SimplexCategory Opposite Simplicial
open AlgebraicTopology.DoldKan

namespace GeneralSphereT.DoldKanExplicitBridge

universe u

/-- The summands of `Γ` in simplicial degree `n` whose chain degree is `r`.
This is the precise finite index type which remains to be naturally
reindexed by cut points (and hence by anchored faces). -/
abbrev GammaIndexAt (n r : ℕ) :=
  {A : SimplicialObject.Splitting.IndexSet
      (Opposite.op (SimplexCategory.mk n)) //
    A.1.unop.len = r}

/-- Monotone surjections between the standard finite ordinals. -/
abbrev OrdinalEpi (n r : ℕ) :=
  {f : ⦋n⦌ ⟶ ⦋r⦌ // Function.Surjective f.toOrderHom}

/-- Replace the variable target object in a `Γ` index by the standard object
of the same length. -/
def gammaIndexToOrdinalEpi {n r : ℕ} (A : GammaIndexAt n r) : OrdinalEpi n r := by
  let h : A.1.1.unop = ⦋r⦌ := SimplexCategory.ext A.2
  refine ⟨A.1.e ≫ eqToHom h, ?_⟩
  rw [← SimplexCategory.epi_iff_surjective]
  infer_instance

/-- Regard an epimorphism between standard finite ordinals as a `Γ` index. -/
def ordinalEpiToGammaIndex {n r : ℕ} (f : OrdinalEpi n r) : GammaIndexAt n r := by
  letI : Epi f.1 := SimplexCategory.epi_iff_surjective.mpr f.2
  exact ⟨SimplicialObject.Splitting.IndexSet.mk f.1, rfl⟩

@[simp]
theorem gammaIndexToOrdinalEpi_ordinalEpiToGammaIndex
    {n r : ℕ} (f : OrdinalEpi n r) :
    gammaIndexToOrdinalEpi (ordinalEpiToGammaIndex f) = f := by
  apply Subtype.ext
  dsimp [gammaIndexToOrdinalEpi, ordinalEpiToGammaIndex,
    SimplicialObject.Splitting.IndexSet.e,
    SimplicialObject.Splitting.IndexSet.mk]
  simp

@[simp]
theorem ordinalEpiToGammaIndex_gammaIndexToOrdinalEpi
    {n r : ℕ} (A : GammaIndexAt n r) :
    ordinalEpiToGammaIndex (gammaIndexToOrdinalEpi A) = A := by
  rcases A with ⟨⟨Δ, ⟨e, he⟩⟩, hdeg⟩
  have hΔ : Δ = op ⦋r⦌ := by
    rw [← unop_inj_iff]
    exact SimplexCategory.ext hdeg
  subst Δ
  have hdeg' : hdeg = rfl := Subsingleton.elim _ _
  cases hdeg'
  apply Subtype.ext
  apply SimplicialObject.Splitting.IndexSet.ext
  dsimp [gammaIndexToOrdinalEpi, ordinalEpiToGammaIndex,
    SimplicialObject.Splitting.IndexSet.e,
    SimplicialObject.Splitting.IndexSet.mk]
  · let u : ⦋r⦌ ⟶ ⦋r⦌ :=
      eqToHom (SimplexCategory.ext (show r = r from rfl))
    change e ≫ u = e
    rw [SimplexCategory.eq_id_of_isIso u, Category.comp_id]
  · rfl

/-- The active `Γ` summands are exactly the monotone epimorphisms between
the corresponding standard finite ordinals. -/
def gammaIndexAtEquivOrdinalEpi (n r : ℕ) :
    GammaIndexAt n r ≃ OrdinalEpi n r where
  toFun := gammaIndexToOrdinalEpi
  invFun := ordinalEpiToGammaIndex
  left_inv := ordinalEpiToGammaIndex_gammaIndexToOrdinalEpi
  right_inv := gammaIndexToOrdinalEpi_ordinalEpiToGammaIndex

/-! ### Epimorphisms and their cut points -/

/-- The finite fiber of a monotone epimorphism over one target vertex. -/
def epiFiber {n r : ℕ} (f : OrdinalEpi n r) (y : Fin (r + 1)) :
    Finset (Fin (n + 1)) :=
  Finset.univ.filter fun x => f.1.toOrderHom x = y

theorem epiFiber_nonempty {n r : ℕ} (f : OrdinalEpi n r) (y : Fin (r + 1)) :
    (epiFiber f y).Nonempty := by
  rcases f.2 y with ⟨x, hx⟩
  exact ⟨x, by simp [epiFiber, hx]⟩

/-- The first vertex in a fiber of a monotone epimorphism.  These first
vertices are the cut points of the corresponding ordered partition. -/
def firstPreimage {n r : ℕ} (f : OrdinalEpi n r) (y : Fin (r + 1)) :
    Fin (n + 1) :=
  (epiFiber f y).min' (epiFiber_nonempty f y)

@[simp]
theorem map_firstPreimage {n r : ℕ} (f : OrdinalEpi n r) (y : Fin (r + 1)) :
    f.1.toOrderHom (firstPreimage f y) = y := by
  exact (Finset.mem_filter.mp
    ((epiFiber f y).min'_mem (epiFiber_nonempty f y))).2

theorem firstPreimage_le_of_mem {n r : ℕ} (f : OrdinalEpi n r)
    {y : Fin (r + 1)} {x : Fin (n + 1)} (hx : f.1.toOrderHom x = y) :
    firstPreimage f y ≤ x := by
  exact (epiFiber f y).min'_le x (by simp [epiFiber, hx])

/-- The cut-point map is left adjoint to the original monotone epimorphism. -/
theorem firstPreimage_le_iff {n r : ℕ} (f : OrdinalEpi n r)
    (y : Fin (r + 1)) (x : Fin (n + 1)) :
    firstPreimage f y ≤ x ↔ y ≤ f.1.toOrderHom x := by
  constructor
  · intro h
    simpa only [map_firstPreimage] using f.1.toOrderHom.monotone h
  · intro h
    rcases f.2 y with ⟨z, hz⟩
    by_cases hzx : z ≤ x
    · exact (firstPreimage_le_of_mem f hz).trans hzx
    · have hxz : x < z := lt_of_not_ge hzx
      have hle : f.1.toOrderHom x ≤ y := by
        simpa only [hz] using f.1.toOrderHom.monotone hxz.le
      have hxy : f.1.toOrderHom x = y := le_antisymm hle h
      exact firstPreimage_le_of_mem f hxy

theorem firstPreimage_strictMono {n r : ℕ} (f : OrdinalEpi n r) :
    StrictMono (firstPreimage f) := by
  intro y z hyz
  apply lt_of_not_ge
  intro h
  have hzy : z ≤ y := by
    simpa only [map_firstPreimage] using f.1.toOrderHom.monotone h
  exact (not_le_of_gt hyz) hzy

theorem ordinalEpi_map_zero {n r : ℕ} (f : OrdinalEpi n r) :
    f.1.toOrderHom 0 = 0 := by
  rcases f.2 0 with ⟨x, hx⟩
  exact le_antisymm (by
    simpa only [hx] using f.1.toOrderHom.monotone (Fin.zero_le x)) (Fin.zero_le _)

@[simp]
theorem firstPreimage_zero {n r : ℕ} (f : OrdinalEpi n r) :
    firstPreimage f 0 = 0 := by
  apply le_antisymm
  · apply firstPreimage_le_of_mem
    exact ordinalEpi_map_zero f
  · exact Fin.zero_le _

/-- The abstract simplicial complex underlying the standard `n`-simplex. -/
abbrev standardSimplex (n : ℕ) : AbstractSimplicialComplex (Fin (n + 1)) := ⊤

/-- The paper's degree-`k` cochains on the standard `n`-simplex. -/
abbrev StandardCochain (n k : ℕ) (G : Type*) [AddCommGroup G] :=
  SimplicialCochain.Cochain (standardSimplex n) k G

/-- A nondegenerate `k`-face of `Δⁿ`, written as its increasing vertex map. -/
abbrev FaceEmbedding (n k : ℕ) := Fin (k + 1) ↪o Fin (n + 1)

/-- Forgetting the increasing enumeration of a face gives its vertex set. -/
def faceEmbeddingToSimplex (n k : ℕ) :
    FaceEmbedding n k → SimplicialCochain.Simplex (standardSimplex n) k :=
  fun f =>
    ⟨(Set.finite_range f).toFinset,
      ⟨by
        change (Set.finite_range f).toFinset.Nonempty
        exact (Set.finite_range f).toFinset_nonempty.mpr (Set.range_nonempty f),
       by
        rw [Set.Finite.card_toFinset]
        simpa using Set.card_range_of_injective f.injective⟩⟩

/-- Increasing enumeration of the vertices of a face. -/
def simplexToFaceEmbedding (n k : ℕ)
    (s : SimplicialCochain.Simplex (standardSimplex n) k) : FaceEmbedding n k :=
  s.1.orderEmbOfFin s.2.2

/-- The canonical equivalence between increasing injections and ordinary
oriented faces of the standard simplex. -/
def faceEmbeddingEquivSimplex (n k : ℕ) :
    FaceEmbedding n k ≃ SimplicialCochain.Simplex (standardSimplex n) k where
  toFun := faceEmbeddingToSimplex n k
  invFun := simplexToFaceEmbedding n k
  left_inv f := by
    symm
    apply Finset.orderEmbOfFin_unique'
    intro i
    simp [faceEmbeddingToSimplex]
  right_inv s := by
    apply Subtype.ext
    ext x
    simp [faceEmbeddingToSimplex, simplexToFaceEmbedding]

/-- Ordinary cochains, expressed in the increasing-injection coordinates
used by the simplex category. -/
def cochainFaceEmbeddingLinearEquiv (n k : ℕ) (G : Type*) [AddCommGroup G] :
    StandardCochain n k G ≃ₗ[ℤ] (FaceEmbedding n k → G) :=
  (Finsupp.domLCongr (faceEmbeddingEquivSimplex n k).symm).trans
    (Finsupp.linearEquivFunOnFinite ℤ G (FaceEmbedding n k))

@[simp]
theorem cochainFaceEmbeddingLinearEquiv_apply
    (n k : ℕ) (G : Type*) [AddCommGroup G]
    (c : StandardCochain n k G) (f : FaceEmbedding n k) :
    cochainFaceEmbeddingLinearEquiv n k G c f =
      c (faceEmbeddingEquivSimplex n k f) :=
  rfl

/-- Delete the `i`th vertex from an increasing face map. -/
def deleteFaceVertex {n k : ℕ} (f : FaceEmbedding n (k + 1))
    (i : Fin (k + 2)) : FaceEmbedding n k :=
  (Fin.succAboveOrderEmb i).trans f

/-- Simplicial coboundary in increasing-injection coordinates. -/
def orderedCoboundary (n k : ℕ) (G : Type*) [AddCommGroup G] :
    (FaceEmbedding n k → G) →ₗ[ℤ] (FaceEmbedding n (k + 1) → G) where
  toFun c f := ∑ i : Fin (k + 2), (-1 : ℤ) ^ (i : ℕ) • c (deleteFaceVertex f i)
  map_add' c c' := by
    ext f
    simp only [Pi.add_apply, smul_add, Finset.sum_add_distrib]
  map_smul' z c := by
    ext f
    simp [Finset.smul_sum, smul_smul, mul_comm]

@[simp]
theorem orderedCoboundary_apply
    (n k : ℕ) (G : Type*) [AddCommGroup G]
    (c : FaceEmbedding n k → G) (f : FaceEmbedding n (k + 1)) :
    orderedCoboundary n k G c f =
      ∑ i : Fin (k + 2), (-1 : ℤ) ^ (i : ℕ) • c (deleteFaceVertex f i) :=
  rfl

/-- In increasing coordinates, the incidence sign of the `i`th deleted
vertex is the familiar `(-1)^i`. -/
theorem incidenceSign_faceEmbeddingToSimplex
    {n k : ℕ} (f : FaceEmbedding n (k + 1)) (i : Fin (k + 2)) :
    SimplicialCochain.incidenceSign (standardSimplex n)
        (faceEmbeddingToSimplex n (k + 1) f) (f i) =
      (-1 : ℤ) ^ (i : ℕ) := by
  unfold SimplicialCochain.incidenceSign
  congr 1
  change ((Set.finite_range f).toFinset.filter fun w => w < f i).card = i
  have hrange : (Set.finite_range f).toFinset =
      (Finset.univ : Finset (Fin (k + 2))).map f.toEmbedding := by
    ext x
    simp
  rw [hrange, Finset.filter_map, Finset.card_map]
  change (Finset.univ.filter fun j : Fin (k + 2) => f j < f i).card = i
  have hfilter : (Finset.univ.filter fun j : Fin (k + 2) => f j < f i) =
      Finset.Iio i := by
    ext j
    simp
  rw [hfilter, Fin.card_Iio]

/-- The abstract-complex operation `eraseVertex` agrees with precomposition
by the corresponding coface injection. -/
theorem eraseVertex_faceEmbeddingToSimplex
    {n k : ℕ} (f : FaceEmbedding n (k + 1)) (i : Fin (k + 2))
    (hi : f i ∈ (faceEmbeddingToSimplex n (k + 1) f).1) :
    SimplicialCochain.eraseVertex (standardSimplex n)
        (faceEmbeddingToSimplex n (k + 1) f) (f i) hi =
      faceEmbeddingToSimplex n k (deleteFaceVertex f i) := by
  apply Subtype.ext
  ext x
  simp only [SimplicialCochain.eraseVertex, Finset.mem_erase,
    faceEmbeddingToSimplex, Set.Finite.mem_toFinset, Set.mem_range,
    deleteFaceVertex, RelEmbedding.coe_trans, Function.comp_apply]
  constructor
  · rintro ⟨hxi, j, rfl⟩
    obtain ⟨j', hj'⟩ := (finSuccAboveEquiv i).surjective
      ⟨j, fun h => hxi (congrArg f h)⟩
    refine ⟨j', ?_⟩
    congr 1
    exact congrArg Subtype.val hj'
  · rintro ⟨j, rfl⟩
    exact ⟨f.injective.ne (Fin.succAbove_ne i j),
      ⟨i.succAbove j, rfl⟩⟩

/-- The vertices of an increasing face are canonically enumerated by its
source finite ordinal. -/
def faceVertexEquiv {n k : ℕ} (f : FaceEmbedding n k) :
    Fin (k + 1) ≃ (faceEmbeddingToSimplex n k f).1 :=
  Equiv.ofBijective
    (fun i => ⟨f i, by simp [faceEmbeddingToSimplex]⟩)
    ⟨fun _ _ h => f.injective (congrArg Subtype.val h), fun x => by
      rcases x with ⟨x, hx⟩
      simp only [faceEmbeddingToSimplex, Set.Finite.mem_toFinset, Set.mem_range] at hx
      rcases hx with ⟨i, rfl⟩
      exact ⟨i, rfl⟩⟩

@[simp]
theorem faceVertexEquiv_apply {n k : ℕ} (f : FaceEmbedding n k) (i : Fin (k + 1)) :
    (faceVertexEquiv f i : Fin (n + 1)) = f i :=
  rfl

/-- The paper's ordered simplicial coboundary is exactly the alternating
coface formula after passing to increasing-injection coordinates. -/
theorem cochainFaceEmbeddingLinearEquiv_coboundary
    (n k : ℕ) (G : Type*) [AddCommGroup G] (c : StandardCochain n k G) :
    cochainFaceEmbeddingLinearEquiv n (k + 1) G
        (SimplicialCochain.coboundary (standardSimplex n) k c) =
      orderedCoboundary n k G (cochainFaceEmbeddingLinearEquiv n k G c) := by
  ext f
  simp only [cochainFaceEmbeddingLinearEquiv_apply,
    SimplicialCochain.coboundary_apply, orderedCoboundary_apply]
  symm
  refine Fintype.sum_equiv (faceVertexEquiv f)
    (fun i : Fin (k + 2) =>
      (-1 : ℤ) ^ (i : ℕ) •
        c (faceEmbeddingEquivSimplex n k (deleteFaceVertex f i)))
    (fun v : (faceEmbeddingToSimplex n (k + 1) f).1 =>
      SimplicialCochain.incidenceSign (standardSimplex n)
          (faceEmbeddingToSimplex n (k + 1) f) v.1 •
        c (SimplicialCochain.eraseVertex (standardSimplex n)
          (faceEmbeddingToSimplex n (k + 1) f) v.1 v.2)) fun i => ?_
  simp only [faceVertexEquiv_apply, incidenceSign_faceEmbeddingToSimplex]
  congr 1
  rw [eraseVertex_faceEmbeddingToSimplex]
  rfl

/-! ## The signed anchored basis used by the disk model -/

/-- Increasing faces which contain the distinguished vertex `0`.  Since the
map is increasing, this is equivalent to saying that its first vertex is `0`. -/
abbrev AnchoredFace (n k : ℕ) := {f : FaceEmbedding n k // f 0 = 0}

/-- Increasing faces which do not contain the distinguished vertex `0`. -/
abbrev UnanchoredFace (n k : ℕ) := {f : FaceEmbedding n k // f 0 ≠ 0}

/-- The cut points of a monotone epimorphism, including the initial vertex
`0`, form an anchored face. -/
def ordinalEpiToAnchoredFace {n r : ℕ} (f : OrdinalEpi n r) : AnchoredFace n r :=
  ⟨OrderEmbedding.ofStrictMono (firstPreimage f) (firstPreimage_strictMono f),
    firstPreimage_zero f⟩

/-- Target indices whose cut point has already occurred by the vertex `x`. -/
def anchoredFloorSet {n r : ℕ} (a : AnchoredFace n r) (x : Fin (n + 1)) :
    Finset (Fin (r + 1)) :=
  Finset.univ.filter fun y => a.1 y ≤ x

theorem anchoredFloorSet_nonempty {n r : ℕ} (a : AnchoredFace n r)
    (x : Fin (n + 1)) : (anchoredFloorSet a x).Nonempty := by
  refine ⟨0, ?_⟩
  simp [anchoredFloorSet, a.2]

/-- The block containing `x`: the greatest cut point which has occurred by
`x`. -/
def anchoredFloor {n r : ℕ} (a : AnchoredFace n r) (x : Fin (n + 1)) :
    Fin (r + 1) :=
  (anchoredFloorSet a x).max' (anchoredFloorSet_nonempty a x)

theorem anchored_le_iff_le_floor {n r : ℕ} (a : AnchoredFace n r)
    (y : Fin (r + 1)) (x : Fin (n + 1)) :
    a.1 y ≤ x ↔ y ≤ anchoredFloor a x := by
  constructor
  · intro h
    exact (anchoredFloorSet a x).le_max' y (by simp [anchoredFloorSet, h])
  · intro h
    have hmem := (anchoredFloorSet a x).max'_mem (anchoredFloorSet_nonempty a x)
    have hfloor : a.1 (anchoredFloor a x) ≤ x := by
      exact (Finset.mem_filter.mp hmem).2
    exact (a.1.monotone h).trans hfloor

theorem anchoredFloor_monotone {n r : ℕ} (a : AnchoredFace n r) :
    Monotone (anchoredFloor a) := by
  intro x x' hxx'
  apply (anchored_le_iff_le_floor a (anchoredFloor a x) x').mp
  exact ((anchored_le_iff_le_floor a (anchoredFloor a x) x).mpr le_rfl).trans hxx'

@[simp]
theorem anchoredFloor_vertex {n r : ℕ} (a : AnchoredFace n r)
    (y : Fin (r + 1)) : anchoredFloor a (a.1 y) = y := by
  apply le_antisymm
  · have hmem := (anchoredFloorSet a (a.1 y)).max'_mem
      (anchoredFloorSet_nonempty a (a.1 y))
    exact a.1.le_iff_le.mp (Finset.mem_filter.mp hmem).2
  · exact (anchored_le_iff_le_floor a y (a.1 y)).mp le_rfl

/-- The monotone epimorphism whose blocks start at the vertices of an
anchored face. -/
def anchoredFaceToOrdinalEpi {n r : ℕ} (a : AnchoredFace n r) : OrdinalEpi n r := by
  let F : Fin (n + 1) →o Fin (r + 1) :=
    ⟨anchoredFloor a, anchoredFloor_monotone a⟩
  refine ⟨SimplexCategory.mkHom F, ?_⟩
  intro y
  exact ⟨a.1 y, anchoredFloor_vertex a y⟩

@[simp]
theorem anchoredFaceToOrdinalEpi_ordinalEpiToAnchoredFace
    {n r : ℕ} (f : OrdinalEpi n r) :
    anchoredFaceToOrdinalEpi (ordinalEpiToAnchoredFace f) = f := by
  apply Subtype.ext
  apply SimplexCategory.Hom.ext'
  ext x
  apply le_antisymm
  · exact (firstPreimage_le_iff f
      (anchoredFloor (ordinalEpiToAnchoredFace f) x) x).mp
      ((anchored_le_iff_le_floor (ordinalEpiToAnchoredFace f)
        (anchoredFloor (ordinalEpiToAnchoredFace f) x) x).mpr le_rfl)
  · exact (anchored_le_iff_le_floor (ordinalEpiToAnchoredFace f)
      (f.1.toOrderHom x) x).mp
      ((firstPreimage_le_iff f (f.1.toOrderHom x) x).mpr le_rfl)

@[simp]
theorem ordinalEpiToAnchoredFace_anchoredFaceToOrdinalEpi
    {n r : ℕ} (a : AnchoredFace n r) :
    ordinalEpiToAnchoredFace (anchoredFaceToOrdinalEpi a) = a := by
  apply Subtype.ext
  ext y
  apply le_antisymm
  · apply firstPreimage_le_of_mem
    exact anchoredFloor_vertex a y
  · apply (anchored_le_iff_le_floor a y
      (firstPreimage (anchoredFaceToOrdinalEpi a) y)).mpr
    have hmap := map_firstPreimage (anchoredFaceToOrdinalEpi a) y
    change anchoredFloor a (firstPreimage (anchoredFaceToOrdinalEpi a) y) = y at hmap
    exact hmap.ge

/-- Monotone epimorphisms `[n] ↠ [r]` are canonically equivalent to the
anchored `r`-faces of `Δⁿ`; the vertices of the face are the first points of
the ordered fibers. -/
def ordinalEpiEquivAnchoredFace (n r : ℕ) : OrdinalEpi n r ≃ AnchoredFace n r where
  toFun := ordinalEpiToAnchoredFace
  invFun := anchoredFaceToOrdinalEpi
  left_inv := anchoredFaceToOrdinalEpi_ordinalEpiToAnchoredFace
  right_inv := ordinalEpiToAnchoredFace_anchoredFaceToOrdinalEpi

/-- The promised cut-point equivalence for the active summands of `Γ`. -/
def gammaIndexAtEquivAnchoredFace (n r : ℕ) :
    GammaIndexAt n r ≃ AnchoredFace n r :=
  (gammaIndexAtEquivOrdinalEpi n r).trans (ordinalEpiEquivAnchoredFace n r)

/-- Adjoin `0` as the first vertex of a face which does not already contain it. -/
def prependZero {n k : ℕ} (f : FaceEmbedding n k) (h : f 0 ≠ 0) :
    FaceEmbedding n (k + 1) :=
  OrderEmbedding.ofStrictMono (Fin.cons (0 : Fin (n + 1)) f) <|
    Fin.strictMono_cons.mpr ⟨fun j => by
      exact (Fin.pos_iff_ne_zero.mpr h).trans_le
        (f.monotone (Fin.zero_le j)), f.strictMono⟩

@[simp]
theorem prependZero_zero {n k : ℕ} (f : FaceEmbedding n k) (h : f 0 ≠ 0) :
    prependZero f h 0 = 0 :=
  rfl

@[simp]
theorem prependZero_succ {n k : ℕ} (f : FaceEmbedding n k) (h : f 0 ≠ 0)
    (i : Fin (k + 1)) : prependZero f h i.succ = f i :=
  rfl

@[simp]
theorem deleteFaceVertex_prependZero_zero
    {n k : ℕ} (f : FaceEmbedding n k) (h : f 0 ≠ 0) :
    deleteFaceVertex (prependZero f h) 0 = f := by
  ext i
  simp [deleteFaceVertex]

theorem deleteFaceVertex_prependZero_succ_anchored
    {n k : ℕ} (f : FaceEmbedding n k) (h : f 0 ≠ 0) (i : Fin (k + 1)) :
    deleteFaceVertex (prependZero f h) i.succ 0 = 0 := by
  simp [deleteFaceVertex]

/-- Deleting the initial vertex of an anchored positive-dimensional face
produces an unanchored face. -/
def anchoredTail {n k : ℕ} (f : AnchoredFace n (k + 1)) : UnanchoredFace n k :=
  ⟨deleteFaceVertex f.1 0, by
    change f.1 1 ≠ 0
    have hpos : (0 : Fin (n + 1)) < f.1 1 := by
      simpa only [f.2] using f.1.strictMono (show (0 : Fin (k + 2)) < 1 by simp)
    exact ne_of_gt hpos⟩

/-- Adjoining and deleting the distinguished vertex are inverse operations. -/
def unanchoredEquivAnchoredSucc (n k : ℕ) :
    UnanchoredFace n k ≃ AnchoredFace n (k + 1) where
  toFun f := ⟨prependZero f.1 f.2, prependZero_zero f.1 f.2⟩
  invFun := anchoredTail
  left_inv f := by
    apply Subtype.ext
    exact deleteFaceVertex_prependZero_zero f.1 f.2
  right_inv f := by
    apply Subtype.ext
    ext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [f.2]
    · simp [anchoredTail, deleteFaceVertex]

/-! ### The signed disk coordinates -/

/-- The two coordinate rows of the disk model: values on anchored `k`-faces
and coboundary values on anchored `(k+1)`-faces. -/
abbrev AnchoredDiskCoordinates (n k : ℕ) (G : Type*) [AddCommGroup G] :=
  (AnchoredFace n k → G) × (AnchoredFace n (k + 1) → G)

/-- Read off the two anchored coordinate rows of a cochain. -/
def toAnchoredDiskCoordinates (n k : ℕ) (G : Type*) [AddCommGroup G] :
    (FaceEmbedding n k → G) →ₗ[ℤ] AnchoredDiskCoordinates n k G where
  toFun c :=
    ⟨fun a => c a.1,
      fun b => orderedCoboundary n k G c b.1⟩
  map_add' c c' := by
    ext a <;> simp [orderedCoboundary, Finset.sum_add_distrib]
  map_smul' z c := by
    ext a <;> simp [orderedCoboundary, Finset.smul_sum, smul_smul]

/-- The alternating sum of all terms except the initial face of a prepended
anchored simplex. -/
def anchoredRemainder {n k : ℕ} {G : Type*} [AddCommGroup G]
    (b : AnchoredFace n k → G) (f : FaceEmbedding n k) (h : f 0 ≠ 0) : G :=
  ∑ i : Fin (k + 1), (-1 : ℤ) ^ ((i : ℕ) + 1) •
    b ⟨deleteFaceVertex (prependZero f h) i.succ,
      deleteFaceVertex_prependZero_succ_anchored f h i⟩

/-- Reconstruct all face values from the two anchored rows.  On a face not
containing `0`, solve the coboundary formula on the simplex obtained by
prepending `0`. -/
def fromAnchoredDiskCoordinates (n k : ℕ) (G : Type*) [AddCommGroup G] :
    AnchoredDiskCoordinates n k G →ₗ[ℤ] (FaceEmbedding n k → G) where
  toFun p f := if h : f 0 = 0 then p.1 ⟨f, h⟩ else
    p.2 ⟨prependZero f h, prependZero_zero f h⟩ - anchoredRemainder p.1 f h
  map_add' p p' := by
    ext f
    by_cases h : f 0 = 0
    · simp [h]
    · simp [h, anchoredRemainder, Finset.sum_add_distrib, sub_add_sub_comm]
  map_smul' z p := by
    ext f
    by_cases h : f 0 = 0
    · simp [h]
    · simp [h, anchoredRemainder, Finset.smul_sum, smul_sub, smul_smul,
        mul_comm]

/-- Coboundary on a simplex obtained by prepending `0`, split into its
initial face and the remaining anchored faces. -/
theorem orderedCoboundary_prependZero
    {n k : ℕ} (G : Type*) [AddCommGroup G]
    (c : FaceEmbedding n k → G) (f : FaceEmbedding n k) (h : f 0 ≠ 0) :
    orderedCoboundary n k G c (prependZero f h) =
      c f + ∑ i : Fin (k + 1), (-1 : ℤ) ^ ((i : ℕ) + 1) •
        c (deleteFaceVertex (prependZero f h) i.succ) := by
  rw [orderedCoboundary_apply, Fin.sum_univ_succ]
  simp only [Fin.val_zero, pow_zero, one_smul,
    deleteFaceVertex_prependZero_zero, Fin.val_succ]

/-- Reading coordinates after reconstruction recovers every cochain. -/
theorem fromAnchoredDiskCoordinates_toAnchoredDiskCoordinates
    (n k : ℕ) (G : Type*) [AddCommGroup G]
    (c : FaceEmbedding n k → G) :
    fromAnchoredDiskCoordinates n k G (toAnchoredDiskCoordinates n k G c) = c := by
  ext f
  by_cases h : f 0 = 0
  · simp [fromAnchoredDiskCoordinates, toAnchoredDiskCoordinates, h]
  · simp only [fromAnchoredDiskCoordinates, toAnchoredDiskCoordinates, h,
      ↓reduceDIte, LinearMap.coe_mk, AddHom.coe_mk,
      anchoredRemainder]
    rw [orderedCoboundary_prependZero]
    abel

/-- Reconstruction also preserves both anchored rows. -/
theorem toAnchoredDiskCoordinates_fromAnchoredDiskCoordinates
    (n k : ℕ) (G : Type*) [AddCommGroup G]
    (p : AnchoredDiskCoordinates n k G) :
    toAnchoredDiskCoordinates n k G (fromAnchoredDiskCoordinates n k G p) = p := by
  apply Prod.ext
  · ext a
    simp [toAnchoredDiskCoordinates, fromAnchoredDiskCoordinates, a.2]
  · ext a
    let f : UnanchoredFace n k := anchoredTail a
    have ha : (unanchoredEquivAnchoredSucc n k) f = a :=
      (unanchoredEquivAnchoredSucc n k).apply_symm_apply a
    change orderedCoboundary n k G (fromAnchoredDiskCoordinates n k G p) a.1 = p.2 a
    rw [← ha]
    change orderedCoboundary n k G (fromAnchoredDiskCoordinates n k G p)
      (prependZero f.1 f.2) = _
    rw [orderedCoboundary_prependZero]
    simp only [fromAnchoredDiskCoordinates, f.2, ↓reduceDIte, LinearMap.coe_mk,
      AddHom.coe_mk, anchoredRemainder,
      deleteFaceVertex_prependZero_succ_anchored]
    abel

/-- The signed anchored basis for cochains on the standard simplex. -/
def cochainEquivAnchoredDiskCoordinates
    (n k : ℕ) (G : Type*) [AddCommGroup G] :
    (FaceEmbedding n k → G) ≃ₗ[ℤ] AnchoredDiskCoordinates n k G where
  toLinearMap := toAnchoredDiskCoordinates n k G
  invFun := fromAnchoredDiskCoordinates n k G
  left_inv := fromAnchoredDiskCoordinates_toAnchoredDiskCoordinates n k G
  right_inv := toAnchoredDiskCoordinates_fromAnchoredDiskCoordinates n k G

/-- Reindex a finite (indeed arbitrary) family along an equivalence. -/
def piReindexLinearEquiv {α β : Type*} (e : α ≃ β)
    (G : Type*) [AddCommGroup G] : (α → G) ≃ₗ[ℤ] (β → G) where
  toFun c b := c (e.symm b)
  invFun c a := c (e a)
  left_inv c := by ext a; simp
  right_inv c := by ext b; simp
  map_add' c c' := rfl
  map_smul' z c := rfl

/-- Coefficients on the active `Γ` summands in one chain degree. -/
abbrev GammaCoordinateFamily (n r : ℕ) (G : Type*) [AddCommGroup G] :=
  GammaIndexAt n r → G

/-- The two nonzero rows of the Dold--Kan disk in simplicial degree `n`. -/
abbrev GammaDiskCoordinateFamily (n k : ℕ) (G : Type*) [AddCommGroup G] :=
  GammaCoordinateFamily n k G × GammaCoordinateFamily n (k + 1) G

/-! ### The actual finite coproduct and its coordinate family -/

/-- All coordinates of Mathlib's chosen finite coproduct model for `Γ C`.
Unlike `GammaCoordinateFamily`, this includes the zero chain degrees. -/
abbrev GammaAllCoordinateFamily
    (C : ChainComplex AddCommGrpCat.{u} ℕ) (n : ℕ) :=
  (A : SimplicialObject.Splitting.IndexSet (op ⦋n⦌)) →
    ↑(Γ₀.Obj.summand C (op ⦋n⦌) A)

/-- The splitting injection used by `Γ₀` is the chosen coproduct injection. -/
theorem gammaCofanInj_eq_sigmaι
    (C : ChainComplex AddCommGrpCat.{u} ℕ) (n : ℕ)
    (A : SimplicialObject.Splitting.IndexSet (op ⦋n⦌)) :
    ((Γ₀.splitting C).cofan (op ⦋n⦌)).inj A =
      Sigma.ι (Γ₀.Obj.summand C (op ⦋n⦌)) A := by
  let i : A.1.unop ⟶ A.1.unop := 𝟙 _
  have hi : Mono i := by dsimp [i]; infer_instance
  change Sigma.ι (Γ₀.Obj.summand C A.1)
      (SimplicialObject.Splitting.IndexSet.id A.1) ≫
      Γ₀.Obj.map C A.e.op =
    Sigma.ι (Γ₀.Obj.summand C (op ⦋n⦌)) A
  have fac : A.e ≫ i = A.e.op.unop ≫
      (SimplicialObject.Splitting.IndexSet.id A.1).e := by
    dsimp [i, SimplicialObject.Splitting.IndexSet.id,
      SimplicialObject.Splitting.IndexSet.e]
  have hmap := @Γ₀.Obj.map_on_summand₀
    AddCommGrpCat _ _ C _ A.1 (op ⦋n⦌)
    (SimplicialObject.Splitting.IndexSet.id A.1)
    A.e.op A.1.unop A.e i A.2.2 hi fac
  rw [hmap]
  have hmono : Γ₀.Obj.Termwise.mapMono C i = 𝟙 _ := by
    dsimp [i]
    exact Γ₀.Obj.Termwise.mapMono_id C A.1.unop
  have hA : SimplicialObject.Splitting.IndexSet.mk A.e = A := by
    simpa [SimplicialObject.Splitting.IndexSet.mk] using A.ext'.symm
  calc
    _ = (𝟙 _) ≫ Sigma.ι (Γ₀.Obj.summand C (op ⦋n⦌))
        (SimplicialObject.Splitting.IndexSet.mk A.e) := by
      exact congrArg (fun f => f ≫ Sigma.ι (Γ₀.Obj.summand C (op ⦋n⦌))
        (SimplicialObject.Splitting.IndexSet.mk A.e)) hmono
    _ = Sigma.ι (Γ₀.Obj.summand C (op ⦋n⦌))
        (SimplicialObject.Splitting.IndexSet.mk A.e) := Category.id_comp _
    _ = _ := by cases hA; rfl

/-- A finite coproduct of abelian groups is its dependent function family.
This is the concrete coordinate chart for the actual object `Γ₀.Obj.obj₂`. -/
def gammaLevelIsoAllCoordinates
    (C : ChainComplex AddCommGrpCat.{u} ℕ) (n : ℕ) :
    Γ₀.Obj.obj₂ C (op ⦋n⦌) ≅
      AddCommGrpCat.of (GammaAllCoordinateFamily C n) :=
  (biproduct.isoCoproduct (Γ₀.Obj.summand C (op ⦋n⦌))).symm ≪≫
    AddCommGrpCat.biproductIsoPi (Γ₀.Obj.summand C (op ⦋n⦌))

/-- Each dependent-function coordinate of the concrete chart is the
corresponding categorical coproduct projection. -/
theorem gammaLevelIsoAllCoordinates_hom_comp_eval
    (C : ChainComplex AddCommGrpCat.{u} ℕ) (n : ℕ)
    [DecidableEq (SimplicialObject.Splitting.IndexSet (op ⦋n⦌))]
    (A : SimplicialObject.Splitting.IndexSet (op ⦋n⦌)) :
    (gammaLevelIsoAllCoordinates C n).hom ≫
        AddCommGrpCat.ofHom
          (Pi.evalAddMonoidHom
            (fun B => ↑(Γ₀.Obj.summand C (op ⦋n⦌) B)) A) =
      Sigma.π (Γ₀.Obj.summand C (op ⦋n⦌)) A := by
  classical
  let f := Γ₀.Obj.summand C (op ⦋n⦌)
  change ((biproduct.isoCoproduct f).symm ≪≫
      AddCommGrpCat.biproductIsoPi f).hom ≫
      AddCommGrpCat.ofHom (Pi.evalAddMonoidHom (fun B => f B) A) =
    Sigma.π f A
  simp only [Iso.trans_hom, Category.assoc]
  rw [← AddCommGrpCat.biproductIsoPi_inv_comp_π f A]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  change (biproduct.isoCoproduct f).inv ≫ biproduct.π f A = Sigma.π f A
  rw [biproduct.isoCoproduct_inv]
  apply colimit.hom_ext
  rintro ⟨B⟩
  by_cases h : B = A
  · subst B
    simp
  · simp [h, biproduct.ι_π_ne, Sigma.ι_π_of_ne]

/-- Underlying additive equivalence of `gammaLevelIsoAllCoordinates`. -/
def gammaLevelEquivAllCoordinates
    (C : ChainComplex AddCommGrpCat.{u} ℕ) (n : ℕ) :
    ↑(Γ₀.Obj.obj₂ C (op ⦋n⦌)) ≃+ GammaAllCoordinateFamily C n :=
  (gammaLevelIsoAllCoordinates C n).addCommGroupIsoToAddEquiv

theorem gammaLevelEquivAllCoordinates_apply
    (C : ChainComplex AddCommGrpCat.{u} ℕ) (n : ℕ)
    [DecidableEq (SimplicialObject.Splitting.IndexSet (op ⦋n⦌))]
    (x : ↑(Γ₀.Obj.obj₂ C (op ⦋n⦌)))
    (A : SimplicialObject.Splitting.IndexSet (op ⦋n⦌)) :
    gammaLevelEquivAllCoordinates C n x A =
      Sigma.π (Γ₀.Obj.summand C (op ⦋n⦌)) A x := by
  exact CategoryTheory.congr_fun
    (gammaLevelIsoAllCoordinates_hom_comp_eval C n A) x

/-- The actual degree-`n` map on Mathlib's chosen `Γ₀` coproduct, written
directly as a coproduct descendent. -/
def gammaLevelMap
    {C D : ChainComplex AddCommGrpCat.{u} ℕ} (f : C ⟶ D) (n : ℕ) :
    Γ₀.Obj.obj₂ C (op ⦋n⦌) ⟶ Γ₀.Obj.obj₂ D (op ⦋n⦌) :=
  Sigma.desc fun A => f.f A.1.unop.len ≫
    Sigma.ι (Γ₀.Obj.summand D (op ⦋n⦌)) A

set_option backward.isDefEq.respectTransparency false in
/-- `gammaLevelMap` is the component of the simplicial map `Γ₀.map f`. -/
theorem gammaLevelMap_eq_denormalizeApp
    {C D : ChainComplex AddCommGrpCat.{u} ℕ} (f : C ⟶ D) (n : ℕ) :
    gammaLevelMap f n = (Γ₀.map f).app (op ⦋n⦌) := by
  change gammaLevelMap f n = (Γ₀.splitting C).desc (op ⦋n⦌)
    (fun A => f.f A.1.unop.len ≫ ((Γ₀.splitting D).cofan (op ⦋n⦌)).inj A)
  apply colimit.hom_ext
  rintro ⟨A⟩
  rw [gammaLevelMap, colimit.ι_desc]
  change f.f A.1.unop.len ≫
      Sigma.ι (Γ₀.Obj.summand D (op ⦋n⦌)) A =
    Sigma.ι (Γ₀.Obj.summand C (op ⦋n⦌)) A ≫
      (Γ₀.splitting C).desc (op ⦋n⦌)
        (fun B => f.f B.1.unop.len ≫
          ((Γ₀.splitting D).cofan (op ⦋n⦌)).inj B)
  symm
  rw [← gammaCofanInj_eq_sigmaι C n A]
  have hdesc := (Γ₀.splitting C).ι_desc (op ⦋n⦌)
    (fun B => f.f B.1.unop.len ≫
      ((Γ₀.splitting D).cofan (op ⦋n⦌)).inj B) A
  have htarget := congrArg (fun g => f.f A.1.unop.len ≫ g)
    (gammaCofanInj_eq_sigmaι D n A)
  exact hdesc.trans htarget

set_option backward.isDefEq.respectTransparency false in
/-- On dependent-function coordinates, `Γ` applies a chain map separately
on every epimorphism-indexed summand. -/
theorem gammaLevelMap_comp_gammaProjection
    {C D : ChainComplex AddCommGrpCat.{u} ℕ} (f : C ⟶ D) (n : ℕ)
    [DecidableEq (SimplicialObject.Splitting.IndexSet (op ⦋n⦌))]
    (A : SimplicialObject.Splitting.IndexSet (op ⦋n⦌)) :
    gammaLevelMap f n ≫
        Sigma.π (Γ₀.Obj.summand D (op ⦋n⦌)) A =
      Sigma.π (Γ₀.Obj.summand C (op ⦋n⦌)) A ≫
        f.f A.1.unop.len := by
  apply colimit.hom_ext
  rintro ⟨B⟩
  simp only [gammaLevelMap, colimit.ι_desc_assoc, Cofan.mk_ι_app]
  change (f.f B.1.unop.len ≫
      Sigma.ι (Γ₀.Obj.summand D (op ⦋n⦌)) B) ≫
        Sigma.π (Γ₀.Obj.summand D (op ⦋n⦌)) A =
    (Sigma.ι (Γ₀.Obj.summand C (op ⦋n⦌)) B ≫
      Sigma.π (Γ₀.Obj.summand C (op ⦋n⦌)) A) ≫ f.f A.1.unop.len
  by_cases h : B = A
  · subst B
    have hD := Sigma.ι_π_eq_id (Γ₀.Obj.summand D (op ⦋n⦌)) A
    have hC := Sigma.ι_π_eq_id (Γ₀.Obj.summand C (op ⦋n⦌)) A
    calc
      _ = f.f A.1.unop.len ≫
          (Sigma.ι (Γ₀.Obj.summand D (op ⦋n⦌)) A ≫
            Sigma.π (Γ₀.Obj.summand D (op ⦋n⦌)) A) :=
        Category.assoc _ _ _
      _ = f.f A.1.unop.len ≫ 𝟙 _ :=
        congrArg (fun g => f.f A.1.unop.len ≫ g) hD
      _ = f.f A.1.unop.len := Category.comp_id _
      _ = (𝟙 _) ≫ f.f A.1.unop.len := (Category.id_comp _).symm
      _ = (Sigma.ι (Γ₀.Obj.summand C (op ⦋n⦌)) A ≫
          Sigma.π (Γ₀.Obj.summand C (op ⦋n⦌)) A) ≫
            f.f A.1.unop.len :=
        congrArg (fun g => g ≫ f.f A.1.unop.len) hC.symm
  · have hD : Sigma.ι (Γ₀.Obj.summand D (op ⦋n⦌)) B ≫
        Sigma.π (Γ₀.Obj.summand D (op ⦋n⦌)) A = 0 :=
      Sigma.ι_π_of_ne _ h
    have hC : Sigma.ι (Γ₀.Obj.summand C (op ⦋n⦌)) B ≫
        Sigma.π (Γ₀.Obj.summand C (op ⦋n⦌)) A = 0 :=
      Sigma.ι_π_of_ne _ h
    rw [Category.assoc, hD, comp_zero, hC, zero_comp]

set_option backward.isDefEq.respectTransparency false in
theorem gammaLevelEquivAllCoordinates_denormalizeMap
    {C D : ChainComplex AddCommGrpCat.{u} ℕ} (f : C ⟶ D) (n : ℕ)
    [DecidableEq (SimplicialObject.Splitting.IndexSet (op ⦋n⦌))]
    (x : ↑(Γ₀.Obj.obj₂ C (op ⦋n⦌)))
    (A : SimplicialObject.Splitting.IndexSet (op ⦋n⦌)) :
    gammaLevelEquivAllCoordinates D n
        (gammaLevelMap f n x) A =
      f.f A.1.unop.len (gammaLevelEquivAllCoordinates C n x A) := by
  rw [gammaLevelEquivAllCoordinates_apply,
    gammaLevelEquivAllCoordinates_apply]
  exact CategoryTheory.congr_fun (gammaLevelMap_comp_gammaProjection f n A) x

/-- The unique nonzero component of the sphere complex. -/
def sphereComponentEquiv (G : AddCommGrpCat.{u}) (q r : ℕ) (h : r = q) :
    ↑((StandardModels.sphereComplex G q).X r) ≃+ ↑G :=
  (HomologicalComplex.singleObjXIsoOfEq
    (ComplexShape.down ℕ) q G r h).addCommGroupIsoToAddEquiv

theorem sphereComponent_eq_zero_of_ne
    (G : AddCommGrpCat.{u}) (q r : ℕ) (h : r ≠ q)
    (x : (StandardModels.sphereComplex G q).X r) : x = 0 := by
  letI : Subsingleton ((StandardModels.sphereComplex G q).X r) :=
    AddCommGrpCat.subsingleton_of_isZero
      (HomologicalComplex.isZero_single_obj_X
        (ComplexShape.down ℕ) q G r h)
  exact Subsingleton.elim _ _

/-- Delete the zero summands of the sphere complex, retaining precisely the
`Γ` coordinates in chain degree `q`. -/
def sphereAllCoordinatesEquivActive
    (G : AddCommGrpCat.{u}) (n q : ℕ) :
    GammaAllCoordinateFamily (StandardModels.sphereComplex G q) n ≃+
      GammaCoordinateFamily n q G where
  toFun x A := sphereComponentEquiv G q A.1.1.unop.len A.2 (x A.1)
  invFun y A := if h : A.1.unop.len = q then
      (sphereComponentEquiv G q A.1.unop.len h).symm (y ⟨A, h⟩)
    else 0
  left_inv x := by
    funext A
    by_cases h : A.1.unop.len = q
    · simp only [h, ↓reduceDIte]
      exact (sphereComponentEquiv G q A.1.unop.len h).symm_apply_apply (x A)
    · simp only [h, ↓reduceDIte]
      exact (sphereComponent_eq_zero_of_ne G q A.1.unop.len h (x A)).symm
  right_inv y := by
    funext A
    change (sphereComponentEquiv G q A.1.1.unop.len A.2)
      (if h : A.1.1.unop.len = q then
        (sphereComponentEquiv G q A.1.1.unop.len h).symm (y ⟨A.1, h⟩)
       else 0) = y A
    simp only [dif_pos A.2]
    exact (sphereComponentEquiv G q A.1.1.unop.len A.2).apply_symm_apply (y A)
  map_add' x y := by
    funext A
    exact map_add (sphereComponentEquiv G q A.1.1.unop.len A.2) (x A.1) (y A.1)

/-- The actual `Γ₀` level of the sphere model, with all categorical zero
summands removed. -/
def sphereGammaLevelEquivCoordinates
    (G : AddCommGrpCat.{u}) (n q : ℕ) :
    ↑(Γ₀.Obj.obj₂ (StandardModels.sphereComplex G q) (op ⦋n⦌)) ≃+
      GammaCoordinateFamily n q G :=
  (gammaLevelEquivAllCoordinates (StandardModels.sphereComplex G q) n).trans
    (sphereAllCoordinatesEquivActive G n q)

/-- The top component of the two-term disk complex. -/
def diskTopComponentEquiv (G : AddCommGrpCat.{u}) (k r : ℕ)
    (h : r = k + 1) :
    ↑((StandardModels.diskComplex G (k + 1)).X r) ≃+ ↑G := by
  subst r
  exact (HomologicalComplex.doubleXIso₀ (𝟙 G)
    (ComplexShape.down_mk (k + 1) k rfl)).addCommGroupIsoToAddEquiv

/-- The bottom component of the two-term disk complex. -/
def diskBottomComponentEquiv (G : AddCommGrpCat.{u}) (k r : ℕ)
    (h : r = k) :
    ↑((StandardModels.diskComplex G (k + 1)).X r) ≃+ ↑G := by
  subst r
  exact (HomologicalComplex.doubleXIso₁ (𝟙 G)
    (ComplexShape.down_mk (k + 1) k rfl) (by omega)).addCommGroupIsoToAddEquiv

theorem diskComponent_eq_zero_of_ne
    (G : AddCommGrpCat.{u}) (k r : ℕ)
    (htop : r ≠ k + 1) (hbottom : r ≠ k)
    (x : (StandardModels.diskComplex G (k + 1)).X r) : x = 0 := by
  letI : Subsingleton ((StandardModels.diskComplex G (k + 1)).X r) :=
    AddCommGrpCat.subsingleton_of_isZero
      (HomologicalComplex.isZero_double_X (𝟙 G)
        (ComplexShape.down_mk (k + 1) k rfl) r htop hbottom)
  exact Subsingleton.elim _ _

/-- Delete the zero summands of the disk complex.  The bottom-degree row is
listed first and the top-degree row second. -/
def diskAllCoordinatesEquivActive
    (G : AddCommGrpCat.{u}) (n k : ℕ) :
    GammaAllCoordinateFamily (StandardModels.diskComplex G (k + 1)) n ≃+
      GammaDiskCoordinateFamily n k G where
  toFun x :=
    ⟨fun A => diskBottomComponentEquiv G k A.1.1.unop.len A.2 (x A.1),
      fun A => diskTopComponentEquiv G k A.1.1.unop.len A.2 (x A.1)⟩
  invFun y A := if htop : A.1.unop.len = k + 1 then
      (diskTopComponentEquiv G k A.1.unop.len htop).symm (y.2 ⟨A, htop⟩)
    else if hbottom : A.1.unop.len = k then
      (diskBottomComponentEquiv G k A.1.unop.len hbottom).symm (y.1 ⟨A, hbottom⟩)
    else 0
  left_inv x := by
    funext A
    by_cases htop : A.1.unop.len = k + 1
    · simp only [htop, ↓reduceDIte]
      exact (diskTopComponentEquiv G k A.1.unop.len htop).symm_apply_apply (x A)
    · by_cases hbottom : A.1.unop.len = k
      · simp only [htop, ↓reduceDIte]
        simp only [hbottom, ↓reduceDIte]
        exact (diskBottomComponentEquiv G k A.1.unop.len hbottom).symm_apply_apply (x A)
      · simp only [htop, hbottom, ↓reduceDIte]
        exact (diskComponent_eq_zero_of_ne G k A.1.unop.len
          htop hbottom (x A)).symm
  right_inv y := by
    apply Prod.ext
    · funext A
      have htop : A.1.1.unop.len ≠ k + 1 := by omega
      change (diskBottomComponentEquiv G k A.1.1.unop.len A.2)
        (if htop' : A.1.1.unop.len = k + 1 then
          (diskTopComponentEquiv G k A.1.1.unop.len htop').symm
            (y.2 ⟨A.1, htop'⟩)
         else if hbottom : A.1.1.unop.len = k then
          (diskBottomComponentEquiv G k A.1.1.unop.len hbottom).symm
            (y.1 ⟨A.1, hbottom⟩)
         else 0) = y.1 A
      simp only [htop, ↓reduceDIte]
      simp only [A.2, ↓reduceDIte]
      exact (diskBottomComponentEquiv G k A.1.1.unop.len A.2).apply_symm_apply (y.1 A)
    · funext A
      change (diskTopComponentEquiv G k A.1.1.unop.len A.2)
        (if htop : A.1.1.unop.len = k + 1 then
          (diskTopComponentEquiv G k A.1.1.unop.len htop).symm
            (y.2 ⟨A.1, htop⟩)
         else if hbottom : A.1.1.unop.len = k then
          (diskBottomComponentEquiv G k A.1.1.unop.len hbottom).symm
            (y.1 ⟨A.1, hbottom⟩)
         else 0) = y.2 A
      simp only [A.2, ↓reduceDIte]
      exact (diskTopComponentEquiv G k A.1.1.unop.len A.2).apply_symm_apply (y.2 A)
  map_add' x y := by
    apply Prod.ext
    · funext A
      exact map_add (diskBottomComponentEquiv G k A.1.1.unop.len A.2)
        (x A.1) (y A.1)
    · funext A
      exact map_add (diskTopComponentEquiv G k A.1.1.unop.len A.2)
        (x A.1) (y A.1)

/-- The actual `Γ₀` level of the disk model, reduced to its two active
coordinate rows. -/
def diskGammaLevelEquivCoordinates
    (G : AddCommGrpCat.{u}) (n k : ℕ) :
    ↑(Γ₀.Obj.obj₂ (StandardModels.diskComplex G (k + 1)) (op ⦋n⦌)) ≃+
      GammaDiskCoordinateFamily n k G :=
  (gammaLevelEquivAllCoordinates (StandardModels.diskComplex G (k + 1)) n).trans
    (diskAllCoordinatesEquivActive G n k)

/-- The top component formula after passing from the categorical copies of
`G` to their underlying additive groups. -/
theorem diskToSphere_componentEquiv_top
    (G : AddCommGrpCat.{u}) (k r : ℕ) (h : r = k + 1)
    (x : (StandardModels.diskComplex G (k + 1)).X r) :
    sphereComponentEquiv G (k + 1) r h
        ((StandardModels.diskToSphere G (k + 1)).f r x) =
      diskTopComponentEquiv G k r h x := by
  subst r
  exact CategoryTheory.congr_fun (StandardModels.diskToSphere_top_component G k) x

set_option backward.isDefEq.respectTransparency false in
/-- In the actual finite-coproduct coordinates, the degreewise map from the
disk model to the sphere model is the second projection. -/
theorem gammaLevelMap_diskToSphere_eq_second
    (G : AddCommGrpCat.{u}) (n k : ℕ)
    [DecidableEq (SimplicialObject.Splitting.IndexSet (op ⦋n⦌))]
    (x : ↑(Γ₀.Obj.obj₂ (StandardModels.diskComplex G (k + 1)) (op ⦋n⦌))) :
    sphereGammaLevelEquivCoordinates G n (k + 1)
        (gammaLevelMap (StandardModels.diskToSphere G (k + 1)) n x) =
      (diskGammaLevelEquivCoordinates G n k x).2 := by
  ext A
  change sphereComponentEquiv G (k + 1) A.1.1.unop.len A.2
      (gammaLevelEquivAllCoordinates
        (StandardModels.sphereComplex G (k + 1)) n
        (gammaLevelMap (StandardModels.diskToSphere G (k + 1)) n x) A.1) =
    diskTopComponentEquiv G k A.1.1.unop.len A.2
      (gammaLevelEquivAllCoordinates
        (StandardModels.diskComplex G (k + 1)) n x A.1)
  rw [gammaLevelEquivAllCoordinates_denormalizeMap]
  exact diskToSphere_componentEquiv_top G k A.1.1.unop.len A.2 _

set_option backward.isDefEq.respectTransparency false in
/-- The same second-projection square stated for the paper's actual
simplicial map `d : L(G,k+1) ⟶ K(G,k+1)`. -/
theorem actualD_eq_secondProjection
    (G : AddCommGrpCat.{u}) (n k : ℕ)
    [DecidableEq (SimplicialObject.Splitting.IndexSet (op ⦋n⦌))]
    (x : ↑(Γ₀.Obj.obj₂ (StandardModels.diskComplex G (k + 1)) (op ⦋n⦌))) :
    sphereGammaLevelEquivCoordinates G n (k + 1)
        ((StandardModels.d G (k + 1)).app (op ⦋n⦌) x) =
      (diskGammaLevelEquivCoordinates G n k x).2 := by
  change sphereGammaLevelEquivCoordinates G n (k + 1)
      ((Γ₀.map (StandardModels.diskToSphere G (k + 1))).app (op ⦋n⦌) x) = _
  rw [← gammaLevelMap_eq_denormalizeApp
    (StandardModels.diskToSphere G (k + 1)) n]
  exact gammaLevelMap_diskToSphere_eq_second G n k x

/-- Reindex the active `Γ` coefficients by their anchored cut-point faces. -/
def gammaCoordinateEquivAnchored (n r : ℕ) (G : Type*) [AddCommGroup G] :
    GammaCoordinateFamily n r G ≃ₗ[ℤ] (AnchoredFace n r → G) :=
  piReindexLinearEquiv (gammaIndexAtEquivAnchoredFace n r) G

/-- Reindex both active rows of the `Γ` disk by anchored faces. -/
def gammaDiskCoordinateEquivAnchored
    (n k : ℕ) (G : Type*) [AddCommGroup G] :
    GammaDiskCoordinateFamily n k G ≃ₗ[ℤ] AnchoredDiskCoordinates n k G :=
  (gammaCoordinateEquivAnchored n k G).prodCongr
    (gammaCoordinateEquivAnchored n (k + 1) G)

/-- The fully explicit signed degreewise bridge for `L`: ordinary
`k`-cochains are linearly equivalent to the two active `Γ` coordinate rows. -/
def standardCochainEquivGammaDiskCoordinates
    (n k : ℕ) (G : Type*) [AddCommGroup G] :
    StandardCochain n k G ≃ₗ[ℤ] GammaDiskCoordinateFamily n k G :=
  (cochainFaceEmbeddingLinearEquiv n k G).trans
    ((cochainEquivAnchoredDiskCoordinates n k G).trans
      (gammaDiskCoordinateEquivAnchored n k G).symm)

/-- In the signed disk coordinates, simplicial coboundary is the second
coordinate.  This is the elementwise compatibility required for the map
`d : L(G,q) → K(G,q)` once the categorical finite coproduct is identified
with its active coordinate family. -/
theorem signedDisk_second_coordinate_eq_coboundary
    (n k : ℕ) (G : Type*) [AddCommGroup G]
    (c : StandardCochain n k G) (a : AnchoredFace n (k + 1)) :
    (cochainEquivAnchoredDiskCoordinates n k G
      (cochainFaceEmbeddingLinearEquiv n k G c)).2 a =
      cochainFaceEmbeddingLinearEquiv n (k + 1) G
        (SimplicialCochain.coboundary (standardSimplex n) k c) a.1 := by
  change orderedCoboundary n k G
      (cochainFaceEmbeddingLinearEquiv n k G c) a.1 = _
  exact congrFun
    (cochainFaceEmbeddingLinearEquiv_coboundary n k G c).symm a.1

end GeneralSphereT.DoldKanExplicitBridge
