import Formalization.Section4RelativeCohomologyExtension
import Formalization.Section4SimplicialConeExtension
import Formalization.CoordinateExtension

set_option linter.style.header false

/-!
# Section 4: the pointed cone pair

This file realizes the pair `X ∪ C_v{b} ⊆ C_vX` in the finite ordered
simplicial-complex model.  The pair has the same ambient vertex type as the
cone, contains the embedded bottom, and adds only the apex--basepoint edge.
Its inclusion is therefore an ordered embedding with identity vertex map.

The cochain on the pair obtained by collapsing the apex to `b` is written
explicitly: in degree zero the apex receives the value at `b`, while in
positive degree extension by zero from the bottom is already the normalized
pullback.  This makes the pointed local condition visible on the nose.
-/

noncomputable section

namespace GeneralSphereT.SimplicialCochain

open GeneralSphereT.PathAlgebra
open GeneralSphereT.PathAlgebra.FacetRestrictionData

variable {V G : Type*} [LinearOrder V] [Fintype V] [AddCommGroup G]
variable (M : AbstractSimplicialComplex V)

local instance (priority := 10000) pointedConePairOptionLE : LE (Option V) :=
  @WithBot.instLE V inferInstance

local instance (priority := 10000) pointedConePairOptionLT : LT (Option V) :=
  @WithBot.instLT V inferInstance

local instance (priority := 10000) pointedConePairOptionLinearOrder :
    LinearOrder (Option V) :=
  @WithBot.linearOrder V inferInstance

/-! ## The literal pair `X ∪ C_v{b}` -/

/-- The bottom together with the apex--basepoint edge, as a subcomplex of
the literal cone. -/
def pointedConePair (b : V) : AbstractSimplicialComplex (Option V) where
  faces := {s | s ∈ simplicialCone M ∧
    ((none : Option V) ∉ s ∨
      s ⊆ ({none, some b} : Finset (Option V)))}
  isRelLowerSet_faces := by
    intro s hs
    refine ⟨(simplicialCone M).isRelLowerSet_faces hs.1 |>.1, ?_⟩
    intro t hts ht
    refine ⟨(simplicialCone M).isRelLowerSet_faces hs.1 |>.2 hts ht, ?_⟩
    rcases hs.2 with hsnone | hsedge
    · exact Or.inl fun hnone => hsnone (hts hnone)
    · exact Or.inr (hts.trans hsedge)
  singleton_mem o := by
    refine ⟨(simplicialCone M).singleton_mem o, ?_⟩
    cases o with
    | none => exact Or.inr (by simp)
    | some x => exact Or.inl (by simp)

@[simp]
theorem mem_pointedConePair (b : V) (s : Finset (Option V)) :
    s ∈ pointedConePair M b ↔
      s ∈ simplicialCone M ∧
        ((none : Option V) ∉ s ∨
          s ⊆ ({none, some b} : Finset (Option V))) :=
  Iff.rfl

/-- The pointed pair is literally a subcomplex of the cone. -/
theorem pointedConePair_le_cone (b : V) :
    pointedConePair M b ≤ simplicialCone M :=
  fun _ hs => hs.1

/-- Inclusion of the pointed pair into the cone.  It is the identity on the
common ambient vertex type. -/
def pointedConePairInclusion (b : V) :
    OrderedSimplicialMap (pointedConePair M b) (simplicialCone M) where
  toOrderEmbedding := OrderEmbedding.id _
  map_mem := by
    intro s hs
    have himage : s.map (OrderEmbedding.id (Option V)).toEmbedding = s := by
      ext o
      simp
    rw [himage]
    exact pointedConePair_le_cone M b hs

/-- Inclusion of the bottom into the pointed pair. -/
def pointedConePairBottomInclusion (b : V) :
    OrderedSimplicialMap M (pointedConePair M b) where
  toOrderEmbedding := coneBottomOrderEmbedding
  map_mem := by
    intro s hs
    rw [mem_pointedConePair]
    refine ⟨(coneBottomInclusion M).map_mem hs, Or.inl ?_⟩
    intro hnone
    rcases Finset.mem_map.mp hnone with ⟨x, _hx, h⟩
    exact Option.some_ne_none x h

/-- The distinguished edge as a simplex of the pointed pair. -/
def pointedConePairEdge (b : V) : NonemptySimplex (pointedConePair M b) :=
  ⟨(coneBasepointEdgeFacet M b).1, by
    rw [mem_pointedConePair]
    refine ⟨(coneBasepointEdgeFacet M b).2, Or.inr ?_⟩
    intro o ho
    simpa [coneBasepointEdgeFacet, basepointFacet] using ho⟩

@[simp]
theorem pointedConePairEdge_val (b : V) :
    (pointedConePairEdge M b).1 =
      (coneBasepointEdgeFacet M b).1 :=
  rfl

/-- Under pair inclusion, the distinguished edge is the same distinguished
edge in the cone. -/
@[simp]
theorem pointedConePairInclusion_mapFacet_edge (b : V) :
    (pointedConePairInclusion M b).mapFacet (pointedConePairEdge M b) =
      coneBasepointEdgeFacet M b := by
  apply Subtype.ext
  simp [OrderedSimplicialMap.mapFacet, pointedConePairInclusion]

/-! ## Collapse of the pair to the bottom on normalized cochains -/

namespace OrderedSimplicialMap

variable {A : AbstractSimplicialComplex V}
variable {Z : AbstractSimplicialComplex (Option V)}

/-- Extension by zero is additive, although the earlier fibrewise argument
only needed it as a set-theoretic section. -/
theorem extendCochainByZero_add
    (F : OrderedSimplicialMap A Z) (n : ℕ)
    (c c' : Cochain A n G) :
    F.extendCochainByZero n (c + c') =
      F.extendCochainByZero n c + F.extendCochainByZero n c' := by
  ext τ
  classical
  by_cases h : ∃ σ : Simplex A n, F.mapSimplex σ = τ
  · rcases h with ⟨σ, rfl⟩
    simp
  · have hz : ∀ c : Cochain A n G,
        F.extendCochainByZero n c τ = 0 := by
      intro c
      simp only [extendCochainByZero,
        Finsupp.equivFunOnFinite_symm_apply_apply]
      exact dite_eq_right h
    rw [hz (c + c')]
    change 0 = F.extendCochainByZero n c τ +
      F.extendCochainByZero n c' τ
    rw [hz c, hz c']
    simp

/-- Pointwise zero outside the image of the simplicial embedding. -/
theorem extendCochainByZero_apply_of_not_mem_range
    (F : OrderedSimplicialMap A Z) (n : ℕ)
    (c : Cochain A n G) (τ : Simplex Z n)
    (hτ : ¬ ∃ σ : Simplex A n, F.mapSimplex σ = τ) :
    F.extendCochainByZero n c τ = 0 := by
  classical
  simp only [extendCochainByZero,
    Finsupp.equivFunOnFinite_symm_apply_apply]
  exact dite_eq_right hτ

end OrderedSimplicialMap

/-- The normalized cochain pullback along the collapse
`X ∪ C_v{b} → X`.  In degree zero the apex is assigned the value at `b`;
in positive degrees it is extension by zero from the bottom. -/
def pointedConePairCochain (b : V) (n : ℕ) :
    Cochain M n G → Cochain (pointedConePair M b) n G :=
  match n with
  | 0 => fun c =>
      (pointedConePairBottomInclusion M b).extendCochainByZero 0 c +
        Finsupp.single (basepointSimplex (pointedConePair M b) none)
          (c (basepointSimplex M b))
  | _ + 1 => fun c =>
      (pointedConePairBottomInclusion M b).extendCochainByZero _ c

@[simp]
theorem pointedConePairCochain_zero (b : V) (n : ℕ) :
    pointedConePairCochain (G := G) M b n 0 = 0 := by
  cases n with
  | zero =>
      ext τ
      simp [pointedConePairCochain]
  | succ n =>
      exact OrderedSimplicialMap.extendCochainByZero_zero
        (pointedConePairBottomInclusion M b) (n + 1)

@[simp]
theorem pointedConePairCochain_add (b : V) (n : ℕ)
    (c c' : Cochain M n G) :
    pointedConePairCochain M b n (c + c') =
      pointedConePairCochain M b n c +
        pointedConePairCochain M b n c' := by
  cases n with
  | zero =>
      rw [show pointedConePairCochain M b 0 (c + c') =
          (pointedConePairBottomInclusion M b).extendCochainByZero 0 (c + c') +
            Finsupp.single (basepointSimplex (pointedConePair M b) none)
              ((c + c') (basepointSimplex M b)) by rfl]
      rw [OrderedSimplicialMap.extendCochainByZero_add]
      ext τ
      change
        ((pointedConePairBottomInclusion M b).extendCochainByZero 0 c +
            (pointedConePairBottomInclusion M b).extendCochainByZero 0 c') τ +
          Finsupp.single (basepointSimplex (pointedConePair M b) none)
              ((c + c') (basepointSimplex M b)) τ =
        ((pointedConePairBottomInclusion M b).extendCochainByZero 0 c +
            Finsupp.single (basepointSimplex (pointedConePair M b) none)
              (c (basepointSimplex M b))) τ +
          ((pointedConePairBottomInclusion M b).extendCochainByZero 0 c' +
            Finsupp.single (basepointSimplex (pointedConePair M b) none)
              (c' (basepointSimplex M b))) τ
      simp only [Finsupp.add_apply]
      by_cases hτ : basepointSimplex (pointedConePair M b) none = τ
      · simp [hτ]
        abel
      · simp [hτ]
  | succ n =>
      exact OrderedSimplicialMap.extendCochainByZero_add
        (pointedConePairBottomInclusion M b) (n + 1) c c'

/-- Additive-map packaging of the pointed-pair cochain construction. -/
def pointedConePairCochainAddHom (b : V) (n : ℕ) :
    Cochain M n G →+ Cochain (pointedConePair M b) n G where
  toFun := pointedConePairCochain M b n
  map_zero' := pointedConePairCochain_zero M b n
  map_add' := pointedConePairCochain_add M b n

/-- A bottom simplex can never be the apex vertex. -/
theorem bottomMapSimplex_ne_apex (b : V) (σ : Simplex M 0) :
    (pointedConePairBottomInclusion M b).mapSimplex σ ≠
      basepointSimplex (pointedConePair M b) none := by
  intro h
  have hnone : (none : Option V) ∈
      ((pointedConePairBottomInclusion M b).mapSimplex σ).1 := by
    rw [h]
    simp [basepointSimplex]
  change none ∈ σ.1.map coneBottomOrderEmbedding.toEmbedding at hnone
  rcases Finset.mem_map.mp hnone with ⟨x, _hx, hx⟩
  exact Option.some_ne_none x hx

/-- Collapsing the pair and then restricting to the bottom is the identity. -/
@[simp]
theorem pullback_pointedConePairCochain (b : V) (n : ℕ)
    (c : Cochain M n G) :
    (pointedConePairBottomInclusion M b).pullback n
        (pointedConePairCochain M b n c) = c := by
  cases n with
  | zero =>
      ext σ
      rw [OrderedSimplicialMap.pullback_apply]
      change
        (pointedConePairBottomInclusion M b).extendCochainByZero 0 c
              ((pointedConePairBottomInclusion M b).mapSimplex σ) +
            Finsupp.single
              (basepointSimplex (pointedConePair M b) none)
              (c (basepointSimplex M b))
              ((pointedConePairBottomInclusion M b).mapSimplex σ) = c σ
      rw [OrderedSimplicialMap.extendCochainByZero_apply_of_eq]
      simp [bottomMapSimplex_ne_apex M b σ]
  | succ n =>
      exact OrderedSimplicialMap.pullback_extendCochainByZero
        (pointedConePairBottomInclusion M b) (n + 1) c

/-! ## The collapse is a normalized cochain map -/

/-- Every simplex of the pointed pair which avoids the apex is uniquely a
bottom simplex. -/
theorem exists_bottom_simplex_of_apex_not_mem (b : V) (n : ℕ)
    (τ : Simplex (pointedConePair M b) n)
    (hτnone : (none : Option V) ∉ τ.1) :
    ∃ σ : Simplex M n,
      (pointedConePairBottomInclusion M b).mapSimplex σ = τ := by
  let s : Finset V := coneBaseVertices τ.1
  have himage : s.image some = τ.1 := by
    ext o
    cases o with
    | none => simp [hτnone]
    | some x => simp [s, mem_coneBaseVertices]
  have hsne : s.Nonempty := by
    have hτne : τ.1.Nonempty :=
      ((pointedConePair M b).isRelLowerSet_faces τ.2.1).1
    rcases hτne with ⟨o, ho⟩
    cases o with
    | none => exact (hτnone ho).elim
    | some x => exact ⟨x, (mem_coneBaseVertices τ.1 x).mpr ho⟩
  have hsM : s ∈ M := by
    have hcone := (mem_pointedConePair M b τ.1).mp τ.2.1 |>.1
    rcases (mem_simplicialCone M τ.1).mp hcone |>.2 with hs0 | hsM
    · exact (Finset.Nonempty.ne_empty hsne hs0).elim
    · exact hsM
  have hcard : s.card = n + 1 := by
    calc
      s.card = (s.image some).card :=
        (Finset.card_image_of_injective s (Option.some_injective V)).symm
      _ = τ.1.card := congrArg Finset.card himage
      _ = n + 1 := τ.2.2
  let σ : Simplex M n := ⟨s, hsM, hcard⟩
  refine ⟨σ, ?_⟩
  apply Subtype.ext
  change s.map coneBottomOrderEmbedding.toEmbedding = τ.1
  calc
    s.map coneBottomOrderEmbedding.toEmbedding = s.image some := by
      rw [Finset.map_eq_image]
      congr 1
    _ = τ.1 := himage

/-- A simplex of dimension at least two in the pointed pair cannot contain
the apex, since the only non-bottom face is the one-dimensional edge. -/
theorem apex_not_mem_pointedConePair_simplex_succ_succ
    (b : V) (n : ℕ)
    (τ : Simplex (pointedConePair M b) (n + 2)) :
    (none : Option V) ∉ τ.1 := by
  intro hnone
  have hp := (mem_pointedConePair M b τ.1).mp τ.2.1
  rcases hp.2 with havoid | hedge
  · exact havoid hnone
  · have hcard := Finset.card_le_card hedge
    have htwo : ({none, some b} : Finset (Option V)).card = 2 := by simp
    rw [τ.2.2, htwo] at hcard
    omega

/-- The edge as an oriented degree-one simplex. -/
def pointedConePairEdgeSimplex (b : V) :
    Simplex (pointedConePair M b) 1 :=
  ⟨(pointedConePairEdge M b).1, (pointedConePairEdge M b).2, by
    simp [pointedConePairEdge, coneBasepointEdgeFacet, basepointFacet]⟩

/-- A degree-one pair simplex containing the apex is the distinguished edge. -/
theorem eq_pointedConePairEdgeSimplex_of_apex_mem
    (b : V) (τ : Simplex (pointedConePair M b) 1)
    (hτ : (none : Option V) ∈ τ.1) :
    τ = pointedConePairEdgeSimplex M b := by
  apply Subtype.ext
  have hp := (mem_pointedConePair M b τ.1).mp τ.2.1
  rcases hp.2 with havoid | hedge
  · exact (havoid hτ).elim
  · apply Finset.eq_of_subset_of_card_le hedge
    simp [τ.2.2]

/-- Naturality handles the bottom simplices in the cochain-map identity. -/
theorem coboundary_pointedConePairCochain_apply_of_bottom
    (b : V) (n : ℕ) (c : Cochain M n G) (σ : Simplex M (n + 1)) :
    coboundary (pointedConePair M b) n
        (pointedConePairCochain M b n c)
        ((pointedConePairBottomInclusion M b).mapSimplex σ) =
      pointedConePairCochain M b (n + 1) (coboundary M n c)
        ((pointedConePairBottomInclusion M b).mapSimplex σ) := by
  calc
    coboundary (pointedConePair M b) n
          (pointedConePairCochain M b n c)
          ((pointedConePairBottomInclusion M b).mapSimplex σ) =
        coboundary M n
          ((pointedConePairBottomInclusion M b).pullback n
            (pointedConePairCochain M b n c)) σ := by
      exact OrderedSimplicialMap.pullback_coboundary_apply
        (pointedConePairBottomInclusion M b) n
          (pointedConePairCochain M b n c) σ
    _ = coboundary M n c σ := by
      rw [pullback_pointedConePairCochain]
    _ = pointedConePairCochain M b (n + 1) (coboundary M n c)
          ((pointedConePairBottomInclusion M b).mapSimplex σ) := by
      symm
      exact OrderedSimplicialMap.extendCochainByZero_apply_of_eq
        (pointedConePairBottomInclusion M b) (n + 1)
          (coboundary M n c) σ

/-- The collapsed zero-cochain has the same basepoint value at both endpoints
of the distinguished edge. -/
theorem pointedConePairCochain_zero_erase_edge
    (b : V) (c : Cochain M 0 G) :
    ∀ v : (pointedConePairEdgeSimplex M b).1,
      pointedConePairCochain M b 0 c
          (eraseVertex (pointedConePair M b)
            (pointedConePairEdgeSimplex M b) v.1 v.2) =
        c (basepointSimplex M b) := by
  rintro ⟨v, hv⟩
  have hv' : v = none ∨ v = some b := by
    simpa [pointedConePairEdgeSimplex, pointedConePairEdge,
      coneBasepointEdgeFacet, basepointFacet] using hv
  rcases hv' with rfl | rfl
  · have herase :
        eraseVertex (pointedConePair M b) (pointedConePairEdgeSimplex M b)
            none (by simp [pointedConePairEdgeSimplex, pointedConePairEdge,
              coneBasepointEdgeFacet, basepointFacet]) =
          (pointedConePairBottomInclusion M b).mapSimplex
            (basepointSimplex M b) := by
      apply Subtype.ext
      change ({none, some b} : Finset (Option V)).erase none = {some b}
      simp
    rw [herase]
    change
      (pointedConePairBottomInclusion M b).extendCochainByZero 0 c
            ((pointedConePairBottomInclusion M b).mapSimplex
              (basepointSimplex M b)) +
          Finsupp.single (basepointSimplex (pointedConePair M b) none)
              (c (basepointSimplex M b))
            ((pointedConePairBottomInclusion M b).mapSimplex
              (basepointSimplex M b)) = c (basepointSimplex M b)
    rw [OrderedSimplicialMap.extendCochainByZero_apply_of_eq]
    simp [bottomMapSimplex_ne_apex M b (basepointSimplex M b)]
  · have herase :
        eraseVertex (pointedConePair M b) (pointedConePairEdgeSimplex M b)
            (some b) (by simp [pointedConePairEdgeSimplex,
              pointedConePairEdge, coneBasepointEdgeFacet,
              basepointFacet]) =
          basepointSimplex (pointedConePair M b) none := by
      apply Subtype.ext
      change ({none, some b} : Finset (Option V)).erase (some b) = {none}
      ext o
      cases o <;> simp
    rw [herase]
    change
      (pointedConePairBottomInclusion M b).extendCochainByZero 0 c
            (basepointSimplex (pointedConePair M b) none) +
          Finsupp.single (basepointSimplex (pointedConePair M b) none)
              (c (basepointSimplex M b))
            (basepointSimplex (pointedConePair M b) none) =
        c (basepointSimplex M b)
    rw [OrderedSimplicialMap.extendCochainByZero_apply_of_not_mem_range]
    · simp
    · rintro ⟨σ, hσ⟩
      exact bottomMapSimplex_ne_apex M b σ hσ

/-- On the only new one-simplex, the two endpoint values agree, so its
degree-zero coboundary is zero. -/
theorem coboundary_pointedConePairCochain_zero_edge
    (b : V) (c : Cochain M 0 G) :
    coboundary (pointedConePair M b) 0
        (pointedConePairCochain M b 0 c)
        (pointedConePairEdgeSimplex M b) = 0 := by
  rw [coboundary_apply]
  simp_rw [pointedConePairCochain_zero_erase_edge M b c]
  have hconstant := congrArg
    (fun z : Cochain (pointedConePair M b) 1 G =>
      z (pointedConePairEdgeSimplex M b))
    (coboundary_constantCochain (pointedConePair M b)
      (c (basepointSimplex M b)))
  rw [coboundary_apply] at hconstant
  exact hconstant

/-- The explicit collapse cochain strictly commutes with coboundary. -/
theorem coboundary_pointedConePairCochain (b : V) (n : ℕ)
    (c : Cochain M n G) :
    coboundary (pointedConePair M b) n
        (pointedConePairCochain M b n c) =
      pointedConePairCochain M b (n + 1) (coboundary M n c) := by
  ext τ
  cases n with
  | zero =>
      by_cases hnone : (none : Option V) ∈ τ.1
      · have hτ := eq_pointedConePairEdgeSimplex_of_apex_mem M b τ hnone
        subst τ
        rw [coboundary_pointedConePairCochain_zero_edge]
        symm
        change
          (pointedConePairBottomInclusion M b).extendCochainByZero 1
              (coboundary M 0 c) (pointedConePairEdgeSimplex M b) = 0
        apply OrderedSimplicialMap.extendCochainByZero_apply_of_not_mem_range
        intro h
        rcases h with ⟨σ, hσ⟩
        have hapex : (none : Option V) ∈
            ((pointedConePairBottomInclusion M b).mapSimplex σ).1 := by
          rw [hσ]
          simp [pointedConePairEdgeSimplex, pointedConePairEdge,
            coneBasepointEdgeFacet, basepointFacet]
        change none ∈ σ.1.map coneBottomOrderEmbedding.toEmbedding at hapex
        rcases Finset.mem_map.mp hapex with ⟨x, _hx, hx⟩
        exact Option.some_ne_none x hx
      · rcases exists_bottom_simplex_of_apex_not_mem M b 1 τ hnone with
          ⟨σ, rfl⟩
        exact coboundary_pointedConePairCochain_apply_of_bottom M b 0 c σ
  | succ n =>
      have hnone := apex_not_mem_pointedConePair_simplex_succ_succ M b n τ
      rcases exists_bottom_simplex_of_apex_not_mem M b (n + 2) τ hnone with
        ⟨σ, rfl⟩
      exact coboundary_pointedConePairCochain_apply_of_bottom
        M b (n + 1) c σ

/-! ## Relative cohomology of the pair gives the pointed fibrewise lift -/

/-- The direct bottom inclusion factors through the pointed pair, on
cochain pullbacks. -/
theorem coneBottom_pullback_eq_pair_pullback (b : V) (n : ℕ)
    (c : Cochain (simplicialCone M) n G) :
    (coneBottomInclusion M).pullback n c =
      (pointedConePairBottomInclusion M b).pullback n
        ((pointedConePairInclusion M b).pullback n c) := by
  ext σ
  simp only [OrderedSimplicialMap.pullback_apply]
  congr 1
  apply Subtype.ext
  ext o
  simp [OrderedSimplicialMap.mapSimplex, coneBottomInclusion,
    pointedConePairBottomInclusion, pointedConePairInclusion]

/-- The pointed-pair collapse carries cocycles to cocycles. -/
theorem pointedConePairCochain_cocycle (b : V) (n : ℕ)
    (c : Cochain M n G) (hc : coboundary M n c = 0) :
    coboundary (pointedConePair M b) n
        (pointedConePairCochain M b n c) = 0 := by
  rw [coboundary_pointedConePairCochain, hc,
    pointedConePairCochain_zero]

/-- The sole remaining hypothesis from (4.10), now stated for the literal
pair and as the promised `range = ker` equality. -/
abbrev PointedConePairRelativeCohomologyZero (b : V) (n : ℕ) : Prop :=
  (pointedConePairInclusion M b).RelativeCohomologyZeroAtSucc
    (G := G) n

/-- Extend a bottom cocycle to the cone by first gluing it to the pointed
pair and then applying relative exactness of that pair. -/
def pointedConeCocycleExtension (b : V) (n : ℕ)
    (hrel : PointedConePairRelativeCohomologyZero (G := G) M b n)
    (z : (coboundaryToRange (G := G) M n).ker) :
    Cochain (simplicialCone M) n G := by
  have hdc : coboundary M n z.1 = 0 := congrArg Subtype.val z.2
  exact (pointedConePairInclusion M b).extensionWithCoboundary n hrel
    (pointedConePairCochain M b n z.1) 0 (by simp)
    (by simp [pointedConePairCochain_cocycle M b n z.1 hdc])

/-- The chosen cocycle extension restricts to the glued cochain on the whole
pair, not only on the bottom. -/
@[simp]
theorem pair_pullback_pointedConeCocycleExtension
    (b : V) (n : ℕ)
    (hrel : PointedConePairRelativeCohomologyZero (G := G) M b n)
    (z : (coboundaryToRange (G := G) M n).ker) :
    (pointedConePairInclusion M b).pullback n
        (pointedConeCocycleExtension M b n hrel z) =
      pointedConePairCochain M b n z.1 := by
  have hdc : coboundary M n z.1 = 0 := congrArg Subtype.val z.2
  exact (pointedConePairInclusion M b).pullback_extensionWithCoboundary
    n hrel (pointedConePairCochain M b n z.1) 0 (by simp)
    (by simp [pointedConePairCochain_cocycle M b n z.1 hdc])

/-- The chosen extension is a cocycle on the cone. -/
@[simp]
theorem coboundary_pointedConeCocycleExtension
    (b : V) (n : ℕ)
    (hrel : PointedConePairRelativeCohomologyZero (G := G) M b n)
    (z : (coboundaryToRange (G := G) M n).ker) :
    coboundary (simplicialCone M) n
        (pointedConeCocycleExtension M b n hrel z) = 0 := by
  have hdc : coboundary M n z.1 = 0 := congrArg Subtype.val z.2
  exact (pointedConePairInclusion M b).coboundary_extensionWithCoboundary
    n hrel (pointedConePairCochain M b n z.1) 0 (by simp)
    (by simp [pointedConePairCochain_cocycle M b n z.1 hdc])

/-- Relative exactness of the literal pair constructs the cocycle-extension
datum for bottom restriction. -/
def pointedConeCocycleExtensionData (b : V) (n : ℕ)
    (hrel : PointedConePairRelativeCohomologyZero (G := G) M b n) :
    CocycleExtensionData
      (coboundaryToRange (G := G) M n)
      (coboundaryToRange (G := G) (simplicialCone M) n)
      (coneBottomFacetHom (G := G) M n).primitiveMap where
  extend := pointedConeCocycleExtension M b n hrel
  res_extend z := by
    change (coneBottomInclusion M).pullback n
      (pointedConeCocycleExtension M b n hrel z) = z.1
    rw [coneBottom_pullback_eq_pair_pullback,
      pair_pullback_pointedConeCocycleExtension,
      pullback_pointedConePairCochain]
  d_extend z := by
    apply Subtype.ext
    exact coboundary_pointedConeCocycleExtension M b n hrel z

/-- An unrestricted bottom cochain is first glued to the pointed pair and
then extended by zero into the cone. -/
def pointedConeArbitraryCochainLift (b : V) (n : ℕ)
    (c : Cochain M n G) : Cochain (simplicialCone M) n G :=
  (pointedConePairInclusion M b).extendCochainByZero n
    (pointedConePairCochain M b n c)

/-- The arbitrary glued lift is still a strict section of bottom
restriction. -/
@[simp]
theorem coneBottom_pullback_pointedConeArbitraryCochainLift
    (b : V) (n : ℕ) (c : Cochain M n G) :
    (coneBottomInclusion M).pullback n
        (pointedConeArbitraryCochainLift M b n c) = c := by
  rw [coneBottom_pullback_eq_pair_pullback (b := b),
    pointedConeArbitraryCochainLift,
    OrderedSimplicialMap.pullback_extendCochainByZero,
    pullback_pointedConePairCochain]

/-- The fibrewise lift (4.9) constructed from the single relative
`range = ker` condition for `X ∪ C_v{b} ⊆ C_vX`. -/
def pointedConeFiberwiseCochainLift (b : V) (n : ℕ)
    (hrel : PointedConePairRelativeCohomologyZero (G := G) M b n) :
    FiberwiseCochainLift
      (coboundaryToRange (G := G) M n)
      (coboundaryToRange (G := G) (simplicialCone M) n)
      (coneBottomFacetHom (G := G) M n).primitiveMap :=
  FiberwiseCochainLift.ofCocycleExtension
    (coboundaryToRange_surjective (G := G) M n)
    (pointedConeArbitraryCochainLift M b n)
    (coneBottom_pullback_pointedConeArbitraryCochainLift M b n)
    (pointedConeCocycleExtensionData M b n hrel)

/-- The selected fibrewise lift restricts on the entire pointed pair to the
explicit collapse cochain.  This is the key strengthening beyond ordinary
bottom restriction. -/
theorem pair_pullback_pointedConeFiberwiseCochainLift
    (b : V) (n : ℕ)
    (hrel : PointedConePairRelativeCohomologyZero (G := G) M b n)
    (c : Cochain M n G) :
    (pointedConePairInclusion M b).pullback n
        ((pointedConeFiberwiseCochainLift M b n hrel).lift c) =
      pointedConePairCochain M b n c := by
  let hsurj := coboundaryToRange_surjective (G := G) M n
  let rep := chosenFiberRepresentative hsurj
  let rem := cocycleRemainder hsurj c
  change (pointedConePairInclusion M b).pullback n
      (pointedConeArbitraryCochainLift M b n (rep (coboundaryToRange M n c)) +
        pointedConeCocycleExtension M b n hrel rem) =
    pointedConePairCochain M b n c
  rw [map_add, pointedConeArbitraryCochainLift,
    OrderedSimplicialMap.pullback_extendCochainByZero,
    pair_pullback_pointedConeCocycleExtension]
  rw [← pointedConePairCochain_add]
  congr 1
  change chosenFiberRepresentative hsurj (coboundaryToRange M n c) +
      (c - chosenFiberRepresentative hsurj (coboundaryToRange M n c)) = c
  abel

/-! ## Local factorization on the distinguished edge -/

/-- A degree-zero collapse cochain is constant on the two vertices of the
distinguished edge. -/
theorem pointedConePairCochain_zero_on_edge
    (b : V) (c : Cochain M 0 G)
    (η : facesIn (pointedConePair M b) 0 (pointedConePairEdge M b)) :
    pointedConePairCochain M b 0 c η.1 =
      c (basepointSimplex M b) := by
  have hcard : η.1.1.card = 1 := by simpa using η.1.2.2
  obtain ⟨o, ho⟩ := Finset.card_eq_one.mp hcard
  have hoedge : o = none ∨ o = some b := by
    have homem : o ∈ (pointedConePairEdge M b).1 := by
      apply η.2
      simp [ho]
    simpa [pointedConePairEdge, coneBasepointEdgeFacet,
      basepointFacet] using homem
  rcases hoedge with rfl | rfl
  · have hη : η.1 = eraseVertex (pointedConePair M b)
        (pointedConePairEdgeSimplex M b) (some b)
        (by simp [pointedConePairEdgeSimplex, pointedConePairEdge,
          coneBasepointEdgeFacet, basepointFacet]) := by
      apply Subtype.ext
      rw [ho]
      change {none} = ({none, some b} : Finset (Option V)).erase (some b)
      ext x
      cases x <;> simp
    rw [hη]
    exact pointedConePairCochain_zero_erase_edge M b c
      ⟨some b, by simp [pointedConePairEdgeSimplex, pointedConePairEdge,
        coneBasepointEdgeFacet, basepointFacet]⟩
  · have hη : η.1 = eraseVertex (pointedConePair M b)
        (pointedConePairEdgeSimplex M b) none
        (by simp [pointedConePairEdgeSimplex, pointedConePairEdge,
          coneBasepointEdgeFacet, basepointFacet]) := by
      apply Subtype.ext
      rw [ho]
      change {some b} = ({none, some b} : Finset (Option V)).erase none
      simp
    rw [hη]
    exact pointedConePairCochain_zero_erase_edge M b c
      ⟨none, by simp [pointedConePairEdgeSimplex, pointedConePairEdge,
        coneBasepointEdgeFacet, basepointFacet]⟩

/-- In positive degree the normalized collapse cochain is zero on the
distinguished edge. -/
theorem pointedConePairCochain_succ_on_edge
    (b : V) (n : ℕ) (c : Cochain M (n + 1) G)
    (η : facesIn (pointedConePair M b) (n + 1)
      (pointedConePairEdge M b)) :
    pointedConePairCochain M b (n + 1) c η.1 = 0 := by
  change (pointedConePairBottomInclusion M b).extendCochainByZero
    (n + 1) c η.1 = 0
  apply OrderedSimplicialMap.extendCochainByZero_apply_of_not_mem_range
  rintro ⟨σ, hσ⟩
  have hsubset : σ.1 ⊆ {b} := by
    intro x hx
    have hxmap : some x ∈
        ((pointedConePairBottomInclusion M b).mapSimplex σ).1 := by
      change some x ∈ σ.1.map coneBottomOrderEmbedding.toEmbedding
      exact Finset.mem_map.mpr ⟨x, hx, rfl⟩
    rw [hσ] at hxmap
    have hxedge := η.2 hxmap
    have hx' : some x = none ∨ some x = some b := by
      simpa [pointedConePairEdge, coneBasepointEdgeFacet,
        basepointFacet] using hxedge
    rcases hx' with hbad | hxb
    · exact (Option.some_ne_none x hbad).elim
    · simpa using Option.some.inj hxb
  have hcard := Finset.card_le_card hsubset
  rw [σ.2.2] at hcard
  simp at hcard

/-- On the pointed edge, the collapse cochain depends only on restriction to
the bottom basepoint facet. -/
theorem restrict_pointedConePairCochain_eq_of_basepoint_restriction
    (b : V) (n : ℕ) (c c' : Cochain M n G)
    (hcc' : restrictCochain M n (basepointFacet M b) c =
      restrictCochain M n (basepointFacet M b) c') :
    restrictCochain (pointedConePair M b) n (pointedConePairEdge M b)
        (pointedConePairCochain M b n c) =
      restrictCochain (pointedConePair M b) n (pointedConePairEdge M b)
        (pointedConePairCochain M b n c') := by
  cases n with
  | zero =>
      have hb := congrArg
        (fun a : Configuration (facesIn M 0 (basepointFacet M b)) G =>
          a (basepointLocalFace M b)) hcc'
      change c (basepointSimplex M b) = c' (basepointSimplex M b) at hb
      ext η
      simp only [restrictCochain_apply]
      rw [pointedConePairCochain_zero_on_edge,
        pointedConePairCochain_zero_on_edge, hb]
  | succ n =>
      ext η
      simp only [restrictCochain_apply]
      rw [pointedConePairCochain_succ_on_edge,
        pointedConePairCochain_succ_on_edge]

/-- Regard a cone-edge face as the identical face in the pointed pair. -/
def coneEdgeFaceToPair (b : V) (n : ℕ)
    (η : facesIn (simplicialCone M) n (coneBasepointEdgeFacet M b)) :
    facesIn (pointedConePair M b) n (pointedConePairEdge M b) :=
  ⟨⟨η.1.1, by
      rw [mem_pointedConePair]
      exact ⟨η.1.2.1, Or.inr η.2⟩, η.1.2.2⟩, η.2⟩

@[simp]
theorem mapFace_coneEdgeFaceToPair (b : V) (n : ℕ)
    (η : facesIn (simplicialCone M) n (coneBasepointEdgeFacet M b)) :
    (pointedConePairInclusion M b).mapFace (pointedConePairEdge M b)
        (coneEdgeFaceToPair M b n η) = η := by
  apply Subtype.ext
  apply Subtype.ext
  simp [OrderedSimplicialMap.mapFace, OrderedSimplicialMap.mapSimplex,
    pointedConePairInclusion]
  rfl

/-- Equality on the whole pointed pair implies equality after restricting
the corresponding cone cochains to the distinguished edge. -/
theorem restrict_cone_edge_eq_of_pair_pullback_eq
    (b : V) (n : ℕ)
    (x x' : Cochain (simplicialCone M) n G)
    (c c' : Cochain M n G)
    (hx : (pointedConePairInclusion M b).pullback n x =
      pointedConePairCochain M b n c)
    (hx' : (pointedConePairInclusion M b).pullback n x' =
      pointedConePairCochain M b n c')
    (hlocal : restrictCochain M n (basepointFacet M b) c =
      restrictCochain M n (basepointFacet M b) c') :
    restrictCochain (simplicialCone M) n (coneBasepointEdgeFacet M b) x =
      restrictCochain (simplicialCone M) n (coneBasepointEdgeFacet M b) x' := by
  have hpair := restrict_pointedConePairCochain_eq_of_basepoint_restriction
    M b n c c' hlocal
  ext η
  let ηp := coneEdgeFaceToPair M b n η
  have hxη := congrArg (fun a : Cochain (pointedConePair M b) n G => a ηp.1) hx
  have hx'η := congrArg (fun a : Cochain (pointedConePair M b) n G => a ηp.1) hx'
  have hpη := congrArg
    (fun a : Configuration
      (facesIn (pointedConePair M b) n (pointedConePairEdge M b)) G => a ηp)
    hpair
  have hmap := congrArg Subtype.val (mapFace_coneEdgeFaceToPair M b n η)
  change (pointedConePairInclusion M b).mapSimplex ηp.1 = η.1 at hmap
  change x η.1 = x' η.1
  calc
    x η.1 = pointedConePairCochain M b n c ηp.1 := by
      simpa only [OrderedSimplicialMap.pullback_apply, hmap] using hxη
    _ = pointedConePairCochain M b n c' ηp.1 := by
      simpa only [restrictCochain_apply] using hpη
    _ = x' η.1 := by
      simpa only [OrderedSimplicialMap.pullback_apply, hmap] using hx'η.symm

/-- The concrete local factor used by `PointedConeFiberwiseLiftData`: extend
a local basepoint configuration by zero, apply the selected lift, and
restrict it to the cone edge. -/
def pointedConeEdgeLift (b : V) (n : ℕ)
    (hrel : PointedConePairRelativeCohomologyZero (G := G) M b n) :
    Configuration (facesIn M n (basepointFacet M b)) G →
      Configuration
        (facesIn (simplicialCone M) n (coneBasepointEdgeFacet M b)) G :=
  fun a => restrictCochain (simplicialCone M) n
    (coneBasepointEdgeFacet M b)
    ((pointedConeFiberwiseCochainLift M b n hrel).lift
      (coordinateExtension (facesIn M n (basepointFacet M b)) a))

/-- The promised closure of the pointed relative-extension input: the single
relative `range = ker` condition produces all fields, including
`edge_compat`, of `PointedConeFiberwiseLiftData`. -/
def pointedConeFiberwiseLiftDataOfRelativeCohomology
    (b : V) (n : ℕ)
    (hrel : PointedConePairRelativeCohomologyZero (G := G) M b n) :
    PointedConeFiberwiseLiftData (G := G) M b n where
  fiberwise := pointedConeFiberwiseCochainLift M b n hrel
  edgeLift := pointedConeEdgeLift M b n hrel
  edge_compat c := by
    apply restrict_cone_edge_eq_of_pair_pullback_eq M b n
      ((pointedConeFiberwiseCochainLift M b n hrel).lift c)
      ((pointedConeFiberwiseCochainLift M b n hrel).lift
        (coordinateExtension (facesIn M n (basepointFacet M b))
          (restrictCochain M n (basepointFacet M b) c)))
      c
      (coordinateExtension (facesIn M n (basepointFacet M b))
        (restrictCochain M n (basepointFacet M b) c))
    · exact pair_pullback_pointedConeFiberwiseCochainLift M b n hrel c
    · exact pair_pullback_pointedConeFiberwiseCochainLift M b n hrel _
    · exact (coordinateRestriction_coordinateExtension
        (facesIn M n (basepointFacet M b))
        (restrictCochain M n (basepointFacet M b) c)).symm

end GeneralSphereT.SimplicialCochain
