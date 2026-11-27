import Formalization.Section4OrderedComplexSSet
import Formalization.Section3SimplicialConeModel
import Mathlib.AlgebraicTopology.SimplicialSet.Homotopy

set_option linter.style.header false

/-!
# Section 4: contraction of the literal ordered cone

The algebraic extension arguments use the literal complex on `Option V`
with apex `none`.  This file connects that model directly to Mathlib's
simplicial homotopy API.  On an ordered simplex `x` and a simplex of
`Δ[1]`, replace the initial `0`-part of the vertex string by the apex and
leave the `1`-part unchanged.  This defines an actual cylinder contraction
from the constant apex map to the identity.

Consequently the literal `Option V` cone used by the cochain proof is an
honestly contractible simplicial set; no comparison with a separately chosen
geometric realization is needed for the cone criterion.
-/

noncomputable section

open CategoryTheory CategoryTheory.Category Opposite Simplicial
open MonoidalCategory CartesianMonoidalCategory

namespace GeneralSphereT.SimplicialCochain

universe u

variable {V : Type u} [LinearOrder V]
variable (M : AbstractSimplicialComplex V)

local instance (priority := 10000) section4SSetLiteralConeOptionLE :
    LE (Option V) :=
  @WithBot.instLE V inferInstance

local instance (priority := 10000) section4SSetLiteralConeOptionLT :
    LT (Option V) :=
  @WithBot.instLT V inferInstance

local instance (priority := 10000) section4SSetLiteralConeOptionLinearOrder :
    LinearOrder (Option V) :=
  @WithBot.linearOrder V inferInstance

/-- The vertex string used in the cone contraction.  Where the interval
simplex is `0` we use the apex; where it is `1` we retain the original
vertex. -/
def literalConeCylinderOrderHom {n : ℕ}
    (x : Fin (n + 1) →o Option V)
    (t : Δ[1].obj (Opposite.op (SimplexCategory.mk n))) :
    Fin (n + 1) →o Option V where
  toFun i := if SSet.stdSimplex.asOrderHom t i = 0 then none else x i
  monotone' i j hij := by
    by_cases hi : SSet.stdSimplex.asOrderHom t i = 0
    · simp only [hi, ↓reduceIte]
      exact WithBot.LE.bot_le _
    · have hj : SSet.stdSimplex.asOrderHom t j ≠ 0 := by
        intro hj
        have ht := (SSet.stdSimplex.asOrderHom t).monotone hij
        have : SSet.stdSimplex.asOrderHom t i = 0 := by
          exact le_antisymm (by simpa [hj] using ht) (Fin.zero_le _)
        exact hi this
      simp [hi, hj, x.monotone hij]

@[simp]
theorem literalConeCylinderOrderHom_apply {n : ℕ}
    (x : Fin (n + 1) →o Option V)
    (t : Δ[1].obj (Opposite.op (SimplexCategory.mk n)))
    (i : Fin (n + 1)) :
    literalConeCylinderOrderHom x t i =
      if SSet.stdSimplex.asOrderHom t i = 0 then none else x i :=
  rfl

/-- The base vertices occurring during the contraction already occurred in
the original simplex. -/
theorem coneBaseVertices_support_literalConeCylinderOrderHom_subset
    {n : ℕ} (x : Fin (n + 1) →o Option V)
    (t : Δ[1].obj (Opposite.op (SimplexCategory.mk n))) :
    coneBaseVertices
        (orderedSimplexSupport (literalConeCylinderOrderHom x t)) ⊆
      coneBaseVertices (orderedSimplexSupport x) := by
  intro v hv
  rw [mem_coneBaseVertices, mem_orderedSimplexSupport] at hv ⊢
  rcases hv with ⟨i, hi⟩
  refine ⟨i, ?_⟩
  by_cases ht : SSet.stdSimplex.asOrderHom t i = 0
  · have hfalse : (none : Option V) = some v := by
      simp only [literalConeCylinderOrderHom_apply, ht, ↓reduceIte] at hi
      exact hi
    cases hfalse
  · simp only [literalConeCylinderOrderHom_apply, ht, ↓reduceIte] at hi
    exact hi

/-- The cylinder vertex string is a simplex of the literal cone. -/
theorem literalConeCylinderOrderHom_mem
    {n : ℕ}
    (x : (orderedComplexSSet (simplicialCone M)).obj
      (Opposite.op (SimplexCategory.mk n)))
    (t : Δ[1].obj (Opposite.op (SimplexCategory.mk n))) :
    orderedSimplexSupport (literalConeCylinderOrderHom x.1 t) ∈
      simplicialCone M := by
  rw [mem_simplicialCone]
  refine ⟨Finset.image_nonempty.mpr Finset.univ_nonempty, ?_⟩
  let s := coneBaseVertices
    (orderedSimplexSupport (literalConeCylinderOrderHom x.1 t))
  by_cases hs : s = ∅
  · exact Or.inl hs
  · right
    have hsub : s ⊆ coneBaseVertices (orderedSimplexSupport x.1) :=
      coneBaseVertices_support_literalConeCylinderOrderHom_subset x.1 t
    rcases (mem_simplicialCone M (orderedSimplexSupport x.1)).mp x.2 with
      ⟨_, hx⟩
    rcases hx with hxzero | hxM
    · exact False.elim (hs (Finset.Subset.antisymm
        (by simpa [hxzero] using hsub) (Finset.empty_subset _)))
    · exact (M.isRelLowerSet_faces hxM).2 hsub
        (Finset.nonempty_iff_ne_empty.mpr hs)

/-- The actual cylinder map contracting the ordered simplicial set of the
literal cone to its apex. -/
def literalConeCylinderMap :
    orderedComplexSSet (simplicialCone M) ⊗ Δ[1] ⟶
      orderedComplexSSet (simplicialCone M) where
  app Δ := ↾fun z ↦
    ⟨literalConeCylinderOrderHom z.1.1 z.2,
      literalConeCylinderOrderHom_mem M z.1 z.2⟩
  naturality Δ Δ' θ := by
    ext z
    rfl

/-- The apex as a zero-simplex of the literal cone simplicial set. -/
abbrev literalConeApex :
    (orderedComplexSSet (simplicialCone M)).obj
      (Opposite.op (SimplexCategory.mk 0)) :=
  orderedComplexVertex (simplicialCone M) none

/-- The literal cone has an actual simplicial contraction from the constant
apex map to the identity. -/
def literalConeContraction :
    SSet.Homotopy
      (SSet.const (literalConeApex M))
      (𝟙 (orderedComplexSSet (simplicialCone M))) where
  h := literalConeCylinderMap M
  h₀ := by
    change SSet.ι₀ ≫ literalConeCylinderMap M =
      SSet.const (literalConeApex M)
    ext Δ x
    apply Subtype.ext
    apply OrderHom.ext
    funext i
    change (if SSet.stdSimplex.asOrderHom (SSet.ι₀.app Δ x).2 i = 0
      then none else x.1 i) = none
    have ht : SSet.stdSimplex.asOrderHom (SSet.ι₀.app Δ x).2 i = 0 :=
      SSet.ι₀_app_snd_apply x i
    simp only [ht, ↓reduceIte]
  h₁ := by
    change SSet.ι₁ ≫ literalConeCylinderMap M = 𝟙 _
    ext Δ x
    apply Subtype.ext
    apply OrderHom.ext
    funext i
    change (if SSet.stdSimplex.asOrderHom (SSet.ι₁.app Δ x).2 i = 0
      then none else x.1 i) = x.1 i
    have ht : SSet.stdSimplex.asOrderHom (SSet.ι₁.app Δ x).2 i = 1 :=
      SSet.ι₁_app_snd_apply x i
    have ht0 : SSet.stdSimplex.asOrderHom (SSet.ι₁.app Δ x).2 i ≠ 0 := by
      rw [ht]
      decide
    simp only [ht0, ↓reduceIte]
  rel := by
    ext Δ x
    exact False.elim (by simpa using x.1.property)

/-- The initial endpoint of the explicit literal-cone cylinder map.  This
named form is convenient when the contraction is used inside longer
composites. -/
@[reassoc]
theorem ι₀_literalConeCylinderMap :
    SSet.ι₀ ≫ literalConeCylinderMap M =
      SSet.const (literalConeApex M) :=
  SSet.Homotopy.h₀ (literalConeContraction M)

/-- The terminal endpoint of the explicit literal-cone cylinder map. -/
@[reassoc]
theorem ι₁_literalConeCylinderMap :
    SSet.ι₁ ≫ literalConeCylinderMap M =
      𝟙 (orderedComplexSSet (simplicialCone M)) :=
  SSet.Homotopy.h₁ (literalConeContraction M)

end GeneralSphereT.SimplicialCochain
