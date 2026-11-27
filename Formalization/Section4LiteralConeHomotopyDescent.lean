import Formalization.Section4LiteralConeNativeCriterion
import Formalization.Section4DoldKanDiskNativeContraction

set_option linter.style.header false

/-!
# Section 4: the precise reverse interface for the literal cone

The literal `Option V` cone is a quotient of the simplicial cylinder which
identifies more simplices than merely collapsing one endpoint.  Consequently
an arbitrary Mathlib cylinder homotopy does not automatically descend to a
map on the literal cone.

This file isolates the exact additional datum: a factorization of the
cylinder map through the explicit quotient map.  Once that factorization is
given, all endpoint and relative conditions are formal.  In particular this
prevents a native nullhomotopy from being mistaken for a literal-cone
extension in the algebraic argument.
-/

noncomputable section

open CategoryTheory CategoryTheory.Category Opposite Simplicial
open MonoidalCategory CartesianMonoidalCategory

namespace GeneralSphereT.SimplicialCochain

universe u

open GeneralSphereT.Section4
open GeneralSphereT.Section4.UnderlyingSSet
open GeneralSphereT.Section4.RelativeMapping
open GeneralSphereT.Section4.NativeRelativeHomotopyGroup
open GeneralSphereT.StandardModels

variable {V : Type u} [LinearOrder V] [Fintype V]
variable (M : AbstractSimplicialComplex V)

local instance (priority := 10000) literalDescentOptionLE : LE (Option V) :=
  @WithBot.instLE V inferInstance

local instance (priority := 10000) literalDescentOptionLT : LT (Option V) :=
  @WithBot.instLT V inferInstance

local instance (priority := 10000) literalDescentOptionLinearOrder :
    LinearOrder (Option V) :=
  @WithBot.linearOrder V inferInstance

/-- The explicit cylinder-to-literal-cone quotient.  At a vertex it sends
`(x,0)` to the apex and `(x,1)` to the bottom vertex `x`. -/
def literalConeCylinderQuotient :
    orderedComplexSSet M ⊗ Δ[1] ⟶
      orderedComplexSSet (simplicialCone M) where
  app Delta :=
    ↾fun z ↦ (literalConeCylinderMap M).app Delta
      ((literalConeBottomMap M ▷ Δ[1]).app Delta z)
  naturality Delta Delta' theta := by
    ext z
    rfl

theorem literalConeCylinderQuotient_eq :
    literalConeCylinderQuotient M =
      literalConeBottomMap M ▷ Δ[1] ≫ literalConeCylinderMap M := by
  ext Delta z
  rfl

/-- Pointwise naturality of the quotient, kept opaque so downstream descent
proofs do not unfold the two explicit cylinder maps. -/
theorem literalConeCylinderQuotient_naturality_apply
    {Delta Delta' : SimplexCategoryᵒᵖ} (theta : Delta ⟶ Delta')
    (x : (orderedComplexSSet M ⊗ Δ[1]).obj Delta) :
    (literalConeCylinderQuotient M).app Delta'
        ((orderedComplexSSet M ⊗ Δ[1]).map theta x) =
      (orderedComplexSSet (simplicialCone M)).map theta
        ((literalConeCylinderQuotient M).app Delta x) :=
  rfl

/-- The zero endpoint of the quotient is the constant apex map. -/
@[reassoc]
theorem ι₀_literalConeCylinderQuotient :
    SSet.ι₀ ≫ literalConeCylinderQuotient M =
      SSet.const (literalConeApex M) := by
  calc
    SSet.ι₀ ≫ literalConeCylinderQuotient M =
        literalConeBottomMap M ≫ SSet.ι₀ ≫
          literalConeCylinderMap M := by
      rw [literalConeCylinderQuotient_eq, SSet.ι₀_comp_assoc]
    _ = literalConeBottomMap M ≫
        SSet.const (literalConeApex M) := by
      exact congrArg
        (fun k : orderedComplexSSet (simplicialCone M) ⟶
            orderedComplexSSet (simplicialCone M) =>
          literalConeBottomMap M ≫ k)
        (ι₀_literalConeCylinderMap M)
    _ = SSet.const (literalConeApex M) :=
      SSet.comp_const (literalConeBottomMap M) (literalConeApex M)

/-- The one endpoint of the quotient is the literal bottom inclusion. -/
@[reassoc]
theorem ι₁_literalConeCylinderQuotient :
    SSet.ι₁ ≫ literalConeCylinderQuotient M =
      literalConeBottomMap M := by
  calc
    SSet.ι₁ ≫ literalConeCylinderQuotient M =
        literalConeBottomMap M ≫ SSet.ι₁ ≫
          literalConeCylinderMap M := by
      rw [literalConeCylinderQuotient_eq, SSet.ι₁_comp_assoc]
    _ = literalConeBottomMap M ≫
        𝟙 (orderedComplexSSet (simplicialCone M)) := by
      exact congrArg
        (fun k : orderedComplexSSet (simplicialCone M) ⟶
            orderedComplexSSet (simplicialCone M) =>
          literalConeBottomMap M ≫ k)
        (ι₁_literalConeCylinderMap M)
    _ = literalConeBottomMap M := Category.comp_id _

/-! ## Degreewise surjectivity of the literal quotient -/

variable (b : V)

/-- A fallback bottom vertex for a cone simplex: the least bottom vertex
when one occurs, and the fixed vertex `b` for the all-apex simplex. -/
def literalConeSimplexFallback {n : ℕ}
    (z : (orderedComplexSSet (simplicialCone M)).obj (op ⦋n⦌)) : V :=
  let s := coneBaseVertices (orderedSimplexSupport z.1)
  if hs : s.Nonempty then s.min' hs else b

theorem literalConeSimplexFallback_le_of_eq_some {n : ℕ}
    (z : (orderedComplexSSet (simplicialCone M)).obj (op ⦋n⦌))
    (i : Fin (n + 1)) (v : V) (hi : z.1 i = some v) :
    literalConeSimplexFallback M b z ≤ v := by
  let s := coneBaseVertices (orderedSimplexSupport z.1)
  have hv : v ∈ s := by
    rw [mem_coneBaseVertices, mem_orderedSimplexSupport]
    exact ⟨i, hi⟩
  have hs : s.Nonempty := ⟨v, hv⟩
  simp only [literalConeSimplexFallback, s, dif_pos hs]
  exact Finset.min'_le s v hv

/-- Replace every apex entry by the chosen fallback bottom vertex. -/
def literalConeBottomLiftOrderHom {n : ℕ}
    (z : (orderedComplexSSet (simplicialCone M)).obj (op ⦋n⦌)) :
    Fin (n + 1) →o V where
  toFun i := (z.1 i).getD (literalConeSimplexFallback M b z)
  monotone' i j hij := by
    change (z.1 i).getD (literalConeSimplexFallback M b z) ≤
      (z.1 j).getD (literalConeSimplexFallback M b z)
    cases hi : z.1 i with
    | none =>
        cases hj : z.1 j with
        | none =>
            simp only [hi, hj, Option.getD_none]
            exact le_rfl
        | some v =>
            simpa only [hi, hj, Option.getD_none, Option.getD_some] using
              literalConeSimplexFallback_le_of_eq_some M b z j v hj
    | some v =>
        cases hj : z.1 j with
        | none =>
            have h := z.1.monotone hij
            rw [hi, hj] at h
            exact False.elim (WithBot.not_coe_le_bot v h)
        | some w =>
            have h := z.1.monotone hij
            rw [hi, hj] at h
            simpa only [hi, hj, Option.getD_some] using
              (WithBot.coe_le_coe.mp h)

/-- Record exactly which entries of a cone simplex are the apex. -/
def literalConeCutOrderHom {n : ℕ}
    (z : (orderedComplexSSet (simplicialCone M)).obj (op ⦋n⦌)) :
    Fin (n + 1) →o Fin 2 where
  toFun i := if z.1 i = none then 0 else 1
  monotone' i j hij := by
    dsimp
    by_cases hi : z.1 i = none
    · simp [hi]
    · by_cases hj : z.1 j = none
      · have h := z.1.monotone hij
        have : False := by
          cases hzi : z.1 i with
          | none => exact hi hzi
          | some v =>
              rw [hzi, hj] at h
              exact WithBot.not_coe_le_bot v h
        exact False.elim this
      · simp [hi, hj]

/-- The canonical cylinder preimage of a literal cone simplex. -/
def literalConeCylinderPreimage {n : ℕ}
    (z : (orderedComplexSSet (simplicialCone M)).obj (op ⦋n⦌)) :
    (orderedComplexSSet M ⊗ Δ[1]).obj (op ⦋n⦌) := by
  let x : (orderedComplexSSet M).obj (op ⦋n⦌) := ⟨
    literalConeBottomLiftOrderHom M b z, by
      let s := coneBaseVertices (orderedSimplexSupport z.1)
      by_cases hs : s.Nonempty
      · have hsM : s ∈ M := by
          rcases (mem_simplicialCone M
            (orderedSimplexSupport z.1)).mp z.2 with ⟨_, h⟩
          exact h.resolve_left (Finset.nonempty_iff_ne_empty.mp hs)
        apply (M.isRelLowerSet_faces hsM).2
        · intro v hv
          rw [mem_orderedSimplexSupport] at hv
          rcases hv with ⟨i, rfl⟩
          change (z.1 i).getD (literalConeSimplexFallback M b z) ∈ s
          cases hi : z.1 i with
          | none =>
              simp only [Option.getD_none]
              simp only [literalConeSimplexFallback, s, dif_pos hs]
              exact Finset.min'_mem s hs
          | some v =>
              simp only [Option.getD_some]
              rw [mem_coneBaseVertices, mem_orderedSimplexSupport]
              exact ⟨i, hi⟩
        · exact Finset.image_nonempty.mpr Finset.univ_nonempty
      · have hznone : ∀ i, z.1 i = none := by
          intro i
          cases hi : z.1 i with
          | none => rfl
          | some v =>
              exfalso
              apply hs
              refine ⟨v, ?_⟩
              rw [mem_coneBaseVertices, mem_orderedSimplexSupport]
              exact ⟨i, hi⟩
        have hxconst : literalConeBottomLiftOrderHom M b z =
            OrderHom.const _ b := by
          apply OrderHom.ext
          funext i
          change (z.1 i).getD (literalConeSimplexFallback M b z) = b
          rw [hznone i]
          simp [literalConeSimplexFallback, s, hs]
        rw [hxconst]
        have hsupp : orderedSimplexSupport (OrderHom.const (Fin (n + 1)) b) =
            {b} := by
          ext v
          simp [orderedSimplexSupport, eq_comm]
        rw [hsupp]
        exact M.singleton_mem b⟩
  exact (x, SSet.stdSimplex.objMk (literalConeCutOrderHom M z))

theorem literalConeCylinderPreimage_maps_to {n : ℕ}
    (z : (orderedComplexSSet (simplicialCone M)).obj (op ⦋n⦌)) :
    (literalConeCylinderQuotient M).app (op ⦋n⦌)
        (literalConeCylinderPreimage M b z) = z := by
  apply Subtype.ext
  apply OrderHom.ext
  funext i
  rcases Option.eq_none_or_eq_some (z.1 i) with hi | ⟨v, hi⟩
  · have hcut : literalConeCutOrderHom M z i = 0 := by
      change (if z.1 i = none then 0 else 1) = 0
      simp [hi]
    change
      (if literalConeCutOrderHom M z i = 0 then none
        else some ((z.1 i).getD (literalConeSimplexFallback M b z))) = z.1 i
    simp only [hcut, if_pos]
    exact hi.symm
  · have hcut : literalConeCutOrderHom M z i ≠ 0 := by
      change (if z.1 i = none then 0 else 1) ≠ 0
      simp [hi]
    change
      (if literalConeCutOrderHom M z i = 0 then none
        else some ((z.1 i).getD (literalConeSimplexFallback M b z))) = z.1 i
    simp only [hcut, if_neg]
    rw [hi]
    rfl

/-- The canonical cylinder preimage, with an arbitrary simplex-category
index rather than a chosen numeral presentation. -/
def literalConeCylinderPreimageAt
    (b : V) (Delta : SimplexCategoryᵒᵖ)
    (z : (orderedComplexSSet (simplicialCone M)).obj Delta) :
    (orderedComplexSSet M ⊗ Δ[1]).obj Delta := by
  induction Delta using Opposite.rec with
  | _ Delta =>
    induction Delta using SimplexCategory.rec with
    | _ n => exact literalConeCylinderPreimage M b z

theorem literalConeCylinderPreimageAt_maps_to
    (b : V) (Delta : SimplexCategoryᵒᵖ)
    (z : (orderedComplexSSet (simplicialCone M)).obj Delta) :
    (literalConeCylinderQuotient M).app Delta
        (literalConeCylinderPreimageAt M b Delta z) = z := by
  induction Delta using Opposite.rec with
  | _ Delta =>
    induction Delta using SimplexCategory.rec with
    | _ n => exact literalConeCylinderPreimage_maps_to M b z

/-- Every simplex of the literal cone has a cylinder representative. -/
theorem literalConeCylinderQuotient_app_surjective
    (b : V) (Δ : SimplexCategoryᵒᵖ) :
    Function.Surjective ((literalConeCylinderQuotient M).app Δ) := by
  intro z
  exact ⟨literalConeCylinderPreimageAt M b Δ z,
    literalConeCylinderPreimageAt_maps_to M b Δ z⟩

theorem literalConeCylinderQuotient_epi (b : V) :
    Epi (literalConeCylinderQuotient M) := by
  rw [NatTrans.epi_iff_epi_app]
  intro Δ
  rw [epi_iff_surjective]
  exact literalConeCylinderQuotient_app_surjective M b Δ

/-! ## Descent from invariance on quotient fibers -/

variable {Y : SSet.{u}}

/-- A cylinder map descends through the literal cone exactly when it is
constant on every degreewise fiber of the explicit quotient. -/
def LiteralConeFiberInvariant
    (h : orderedComplexSSet M ⊗ Δ[1] ⟶ Y) : Prop :=
  ∀ (Delta : SimplexCategoryᵒᵖ)
      (x y : (orderedComplexSSet M ⊗ Δ[1]).obj Delta),
    (literalConeCylinderQuotient M).app Delta x =
        (literalConeCylinderQuotient M).app Delta y →
      h.app Delta x = h.app Delta y

/-- The descended map, evaluated on the canonical representative of each
literal-cone simplex.  Naturality follows from fiber invariance; the chosen
representative itself need not be natural. -/
def literalConeDescendedMap
    (b : V) (h : orderedComplexSSet M ⊗ Δ[1] ⟶ Y)
    (hinv : LiteralConeFiberInvariant M h) :
    orderedComplexSSet (simplicialCone M) ⟶ Y where
  app Delta := ↾fun y ↦
    h.app Delta (literalConeCylinderPreimageAt M b Delta y)
  naturality Delta Delta' theta := by
    ext y
    symm
    change
      Y.map theta
          (h.app Delta (literalConeCylinderPreimageAt M b Delta y)) =
        h.app Delta'
          (literalConeCylinderPreimageAt M b Delta'
            ((orderedComplexSSet (simplicialCone M)).map theta y))
    have hnat :
        h.app Delta'
            ((orderedComplexSSet M ⊗ Δ[1]).map theta
              (literalConeCylinderPreimageAt M b Delta y)) =
          Y.map theta
            (h.app Delta (literalConeCylinderPreimageAt M b Delta y)) :=
      h.naturality_apply theta
        (literalConeCylinderPreimageAt M b Delta y)
    calc
      _ = h.app Delta'
          ((orderedComplexSSet M ⊗ Δ[1]).map theta
            (literalConeCylinderPreimageAt M b Delta y)) := hnat.symm
      _ = _ := hinv Delta' _ _ (by
        calc
          (literalConeCylinderQuotient M).app Delta'
              ((orderedComplexSSet M ⊗ Δ[1]).map theta
                (literalConeCylinderPreimageAt M b Delta y)) =
              (orderedComplexSSet (simplicialCone M)).map theta
                ((literalConeCylinderQuotient M).app Delta
                  (literalConeCylinderPreimageAt M b Delta y)) :=
            literalConeCylinderQuotient_naturality_apply M theta
              (literalConeCylinderPreimageAt M b Delta y)
          _ = (orderedComplexSSet (simplicialCone M)).map theta y := by
            rw [literalConeCylinderPreimageAt_maps_to]
          _ = (literalConeCylinderQuotient M).app Delta'
              (literalConeCylinderPreimageAt M b Delta'
                ((orderedComplexSSet (simplicialCone M)).map theta y)) := by
            rw [literalConeCylinderPreimageAt_maps_to])

@[reassoc]
theorem literalConeCylinderQuotient_descendedMap
    (b : V) (h : orderedComplexSSet M ⊗ Δ[1] ⟶ Y)
    (hinv : LiteralConeFiberInvariant M h) :
    literalConeCylinderQuotient M ≫
        literalConeDescendedMap M b h hinv = h := by
  ext Delta x
  change h.app Delta
      (literalConeCylinderPreimageAt M b Delta
        ((literalConeCylinderQuotient M).app Delta x)) = h.app Delta x
  exact hinv Delta _ _
    (literalConeCylinderPreimageAt_maps_to M b Delta _)

variable (P : (orderedComplexSSet M).Subcomplex)
variable (A : SimplicialObject AddCommGrpCat.{u})

/-- A genuine extension of a strictly relative map over the literal cone.
The last field says that the extension vanishes along the cone swept out by
the whole source boundary `P`. -/
structure LiteralRelativeExtension
    (f : NativeRelativeMorphism P A) : Type u where
  map : orderedComplexSSet (simplicialCone M) ⟶ underlyingSSet A
  bottom : literalConeBottomMap M ≫ map = f.map
  apex : SSet.const (literalConeApex M) ≫ map =
    (0 : orderedComplexSSet M ⟶ underlyingSSet A)
  rel : P.ι ▷ Δ[1] ≫ literalConeCylinderQuotient M ≫ map =
    fst (P : SSet) Δ[1] ≫ zeroBoundary P A ≫ (zeroSubcomplex A).ι

namespace LiteralRelativeExtension

variable {M P A}
variable {f : NativeRelativeMorphism P A}

/-- A literal relative extension produces an actual native relative
homotopy from zero to the bottom map. -/
def toRelativeHomotopy (E : LiteralRelativeExtension M P A f) :
    SSet.RelativeMorphism.Homotopy
      (0 : NativeRelativeMorphism P A) f where
  h := literalConeCylinderQuotient M ≫ E.map
  h₀ := by
    calc
      SSet.ι₀ ≫ literalConeCylinderQuotient M ≫ E.map =
          SSet.const (literalConeApex M) ≫ E.map := by
        rw [← Category.assoc, ι₀_literalConeCylinderQuotient]
      _ = (0 : orderedComplexSSet M ⟶ underlyingSSet A) := E.apex
      _ = (0 : NativeRelativeMorphism P A).map :=
        (relativeMorphism_zero_map P A).symm
  h₁ := by
    calc
      SSet.ι₁ ≫ literalConeCylinderQuotient M ≫ E.map =
          literalConeBottomMap M ≫ E.map := by
        rw [← Category.assoc, ι₁_literalConeCylinderQuotient]
      _ = f.map := E.bottom
  rel := E.rel

/-- Native class-zero consequence of a genuine literal extension. -/
theorem class_eq_zero (E : LiteralRelativeExtension M P A f) :
    f.homotopyClass =
      (0 : NativeRelativeMorphism P A).homotopyClass :=
  E.toRelativeHomotopy.eq.symm

end LiteralRelativeExtension

/-- The exact extra datum needed to reverse a native relative homotopy into
a literal-cone extension: its cylinder map must factor through the explicit
literal quotient, with the descended apex equal to zero. -/
structure LiteralRelativeHomotopyDescent
    {f : NativeRelativeMorphism P A}
    (H : SSet.RelativeMorphism.Homotopy
      (0 : NativeRelativeMorphism P A) f) : Type u where
  map : orderedComplexSSet (simplicialCone M) ⟶ underlyingSSet A
  quotient : literalConeCylinderQuotient M ≫ map = H.h
  apex : SSet.const (literalConeApex M) ≫ map =
    (0 : orderedComplexSSet M ⟶ underlyingSSet A)

namespace LiteralRelativeHomotopyDescent

variable {M P A}
variable {f : NativeRelativeMorphism P A}
variable {H : SSet.RelativeMorphism.Homotopy
  (0 : NativeRelativeMorphism P A) f}

/-- Once the factorization exists, all bottom and relative conditions of a
literal extension follow formally from the homotopy endpoints. -/
def toLiteralRelativeExtension
    (D : LiteralRelativeHomotopyDescent M P A H) :
    LiteralRelativeExtension M P A f where
  map := D.map
  bottom := by
    calc
      literalConeBottomMap M ≫ D.map =
          (SSet.ι₁ ≫ literalConeCylinderQuotient M) ≫ D.map := by
        rw [ι₁_literalConeCylinderQuotient]
      _ = SSet.ι₁ ≫
          (literalConeCylinderQuotient M ≫ D.map) :=
        Category.assoc _ _ _
      _ = SSet.ι₁ ≫ H.h := by rw [D.quotient]
      _ = f.map := H.h₁
  apex := D.apex
  rel := by
    calc
      P.ι ▷ Δ[1] ≫ literalConeCylinderQuotient M ≫ D.map =
          P.ι ▷ Δ[1] ≫
            (literalConeCylinderQuotient M ≫ D.map) :=
        rfl
      _ = P.ι ▷ Δ[1] ≫ H.h := by rw [D.quotient]
      _ = fst (P : SSet) Δ[1] ≫ zeroBoundary P A ≫
          (zeroSubcomplex A).ι := H.rel

end LiteralRelativeHomotopyDescent

/-! ## The remaining target-specific datum for the Dold--Kan disk -/

/-- The minimal literal-cone datum still required after the reduced-free
Dold--Kan contraction has supplied the actual native relative homotopy. -/
abbrev StandardDiskReducedFreeLiteralDescentData
    (G : AddCommGrpCat.{u}) (q : ℕ)
    (f : NativeRelativeMorphism P (reducedFree (L G (q + 1)))) :=
  LiteralRelativeHomotopyDescent M P (reducedFree (L G (q + 1)))
    (standardDiskReducedFreeRelativeMapContraction P G q f)

/-- A solution of the target-specific descent problem gives the desired
literal-cone extension without any further topological hypothesis. -/
def standardDiskReducedFreeLiteralExtension
    (G : AddCommGrpCat.{u}) (q : ℕ)
    (f : NativeRelativeMorphism P (reducedFree (L G (q + 1))))
    (D : StandardDiskReducedFreeLiteralDescentData M P G q f) :
    LiteralRelativeExtension M P (reducedFree (L G (q + 1))) f :=
  D.toLiteralRelativeExtension

end GeneralSphereT.SimplicialCochain
