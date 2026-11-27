import Formalization.Section4DoubleConeCohomologyShift
import Formalization.Section4NativeTransgression

set_option linter.style.header false
set_option backward.isDefEq.respectTransparency false

/-!
# Section 4: primitive gluing on the double-cone boundary

This file implements the first, genuinely relative step in (4.16).  The two
literal cone faces of `doubleConeBoundary M` are glued at cochain level by
inclusion--exclusion.  The resulting construction is then used to extend a
primitive relation on the inner cone, whose bottom restriction is zero, by
the zero relation on the other cone.
-/

noncomputable section

namespace GeneralSphereT.SimplicialCochain

open GeneralSphereT.PathAlgebra
open GeneralSphereT.PathAlgebra.FacetRestrictionData
open GeneralSphereT.PathAlgebra.FacetRestrictionHom

universe u

variable {V G : Type u} [LinearOrder V] [Fintype V] [AddCommGroup G]

local instance (priority := 10000) doubleGlueOptionLE : LE (Option V) :=
  @WithBot.instLE V inferInstance

local instance (priority := 10000) doubleGlueOptionLT : LT (Option V) :=
  @WithBot.instLT V inferInstance

local instance (priority := 10000) doubleGlueOptionLinearOrder :
    LinearOrder (Option V) := @WithBot.linearOrder V inferInstance

local instance (priority := 10001) doubleGlueOptionOptionLE :
    LE (Option (Option V)) := @WithBot.instLE (Option V) inferInstance

local instance (priority := 10001) doubleGlueOptionOptionLT :
    LT (Option (Option V)) := @WithBot.instLT (Option V) inferInstance

local instance (priority := 10001) doubleGlueOptionOptionLinearOrder :
    LinearOrder (Option (Option V)) :=
  @WithBot.linearOrder (Option V) inferInstance

variable (M : AbstractSimplicialComplex V)

/-- The common equator `M` as a subcomplex of the double-cone boundary. -/
def doubleConeEquatorInclusion :
    OrderedSimplicialMap M (doubleConeBoundary M) :=
  OrderedSimplicialMap.comp (doubleConeInnerBoundaryInclusion M)
    (coneBottomInclusion M)

/-- On the common bottom, the two face embeddings have the same simplex
image. -/
theorem doubleConeFaces_mapSimplex_bottom_eq (n : ℕ)
    (sigma : Simplex M n) :
    (doubleConeInnerBoundaryInclusion M).mapSimplex
        ((coneBottomInclusion M).mapSimplex sigma) =
      (doubleConeOtherBoundaryInclusion M).mapSimplex
        ((coneBottomInclusion M).mapSimplex sigma) := by
  apply Subtype.ext
  ext o
  simp [OrderedSimplicialMap.mapSimplex,
    doubleConeInnerBoundaryInclusion, doubleConeOtherBoundaryInclusion,
    coneBottomInclusion, coneBottomOrderEmbedding,
    doubleConeOtherOrderEmbedding_some]

/-- The equator composite agrees with the other-face composite on every
simplex. -/
theorem doubleConeEquator_mapSimplex_eq_other (n : ℕ)
    (sigma : Simplex M n) :
    (doubleConeEquatorInclusion M).mapSimplex sigma =
      (doubleConeOtherBoundaryInclusion M).mapSimplex
        ((coneBottomInclusion M).mapSimplex sigma) := by
  calc
    _ = (doubleConeInnerBoundaryInclusion M).mapSimplex
          ((coneBottomInclusion M).mapSimplex sigma) :=
      OrderedSimplicialMap.mapSimplex_comp
        (doubleConeInnerBoundaryInclusion M) (coneBottomInclusion M) sigma
    _ = _ := doubleConeFaces_mapSimplex_bottom_eq M n sigma

/-- Pullback from the boundary to the equator may be computed through the
inner face. -/
theorem doubleConeEquator_pullback_eq_inner_bottom (n : ℕ)
    (c : Cochain (doubleConeBoundary M) n G) :
    (doubleConeEquatorInclusion M).pullback n c =
      (coneBottomInclusion M).pullback n
        ((doubleConeInnerBoundaryInclusion M).pullback n c) := by
  ext sigma
  simp only [OrderedSimplicialMap.pullback_apply]
  congr 1
  exact OrderedSimplicialMap.mapSimplex_comp
    (doubleConeInnerBoundaryInclusion M) (coneBottomInclusion M) sigma

/-- Pullback from the boundary to the equator may equally be computed
through the other cone face. -/
theorem doubleConeEquator_pullback_eq_other_bottom (n : ℕ)
    (c : Cochain (doubleConeBoundary M) n G) :
    (doubleConeEquatorInclusion M).pullback n c =
      (coneBottomInclusion M).pullback n
        ((doubleConeOtherBoundaryInclusion M).pullback n c) := by
  ext sigma
  simp only [OrderedSimplicialMap.pullback_apply]
  congr 1
  exact doubleConeEquator_mapSimplex_eq_other M n sigma

/-- The other-face extension, restricted to the inner cone, is extension by
zero from the common bottom. -/
theorem inner_pullback_other_extendCochainByZero (n : ℕ)
    (c : Cochain (simplicialCone M) n G) :
    (doubleConeInnerBoundaryInclusion M).pullback n
        ((doubleConeOtherBoundaryInclusion M).extendCochainByZero n c) =
      (coneBottomInclusion M).extendCochainByZero n
        ((coneBottomInclusion M).pullback n c) := by
  ext sigma
  rw [OrderedSimplicialMap.pullback_apply]
  by_cases hapex : (none : Option V) ∈ sigma.1
  · have hleft :
        (doubleConeOtherBoundaryInclusion M).extendCochainByZero n c
            ((doubleConeInnerBoundaryInclusion M).mapSimplex sigma) = 0 := by
      apply OrderedSimplicialMap.extendCochainByZero_apply_of_not_mem_range
      rintro ⟨rho, hrho⟩
      have houter : (some none : Option (Option V)) ∈
          ((doubleConeInnerBoundaryInclusion M).mapSimplex sigma).1 := by
        change some none ∈ sigma.1.map coneBottomOrderEmbedding.toEmbedding
        exact Finset.mem_map.mpr ⟨none, hapex, rfl⟩
      rw [← hrho] at houter
      change some none ∈
        rho.1.map (doubleConeOtherOrderEmbedding (V := V)).toEmbedding at houter
      rcases Finset.mem_map.mp houter with ⟨o, _ho, hEq⟩
      cases o <;> simp at hEq
    have hright :
        (coneBottomInclusion M).extendCochainByZero n
            ((coneBottomInclusion M).pullback n c) sigma = 0 := by
      apply OrderedSimplicialMap.extendCochainByZero_apply_of_not_mem_range
      rintro ⟨rho, hrho⟩
      have : (none : Option V) ∈
          ((coneBottomInclusion M).mapSimplex rho).1 := by rw [hrho]; exact hapex
      change none ∈ rho.1.map coneBottomOrderEmbedding.toEmbedding at this
      rcases Finset.mem_map.mp this with ⟨v, _hv, hEq⟩
      exact Option.some_ne_none v hEq
    rw [hleft, hright]
  · rcases exists_coneBottom_simplex_of_apex_not_mem M n sigma hapex with
      ⟨rho, hrho⟩
    rw [← hrho]
    have hmap :
        (doubleConeInnerBoundaryInclusion M).mapSimplex
            ((coneBottomInclusion M).mapSimplex rho) =
          (doubleConeOtherBoundaryInclusion M).mapSimplex
            ((coneBottomInclusion M).mapSimplex rho) := by
      exact doubleConeFaces_mapSimplex_bottom_eq M n rho
    rw [hmap, OrderedSimplicialMap.extendCochainByZero_apply_of_eq,
      OrderedSimplicialMap.extendCochainByZero_apply_of_eq,
      OrderedSimplicialMap.pullback_apply]

/-- Symmetrically, the inner-face extension restricts to the other cone as
extension by zero from the common bottom. -/
theorem other_pullback_inner_extendCochainByZero (n : ℕ)
    (c : Cochain (simplicialCone M) n G) :
    (doubleConeOtherBoundaryInclusion M).pullback n
        ((doubleConeInnerBoundaryInclusion M).extendCochainByZero n c) =
      (coneBottomInclusion M).extendCochainByZero n
        ((coneBottomInclusion M).pullback n c) := by
  ext sigma
  rw [OrderedSimplicialMap.pullback_apply]
  by_cases hapex : (none : Option V) ∈ sigma.1
  · have hleft :
        (doubleConeInnerBoundaryInclusion M).extendCochainByZero n c
            ((doubleConeOtherBoundaryInclusion M).mapSimplex sigma) = 0 := by
      apply OrderedSimplicialMap.extendCochainByZero_apply_of_not_mem_range
      rintro ⟨rho, hrho⟩
      have houter : (none : Option (Option V)) ∈
          ((doubleConeOtherBoundaryInclusion M).mapSimplex sigma).1 := by
        change none ∈
          sigma.1.map (doubleConeOtherOrderEmbedding (V := V)).toEmbedding
        exact Finset.mem_map.mpr ⟨none, hapex, rfl⟩
      rw [← hrho] at houter
      change none ∈ rho.1.map coneBottomOrderEmbedding.toEmbedding at houter
      rcases Finset.mem_map.mp houter with ⟨o, _ho, hEq⟩
      exact Option.some_ne_none o hEq
    have hright :
        (coneBottomInclusion M).extendCochainByZero n
            ((coneBottomInclusion M).pullback n c) sigma = 0 := by
      apply OrderedSimplicialMap.extendCochainByZero_apply_of_not_mem_range
      rintro ⟨rho, hrho⟩
      have : (none : Option V) ∈
          ((coneBottomInclusion M).mapSimplex rho).1 := by rw [hrho]; exact hapex
      change none ∈ rho.1.map coneBottomOrderEmbedding.toEmbedding at this
      rcases Finset.mem_map.mp this with ⟨v, _hv, hEq⟩
      exact Option.some_ne_none v hEq
    rw [hleft, hright]
  · rcases exists_coneBottom_simplex_of_apex_not_mem M n sigma hapex with
      ⟨rho, hrho⟩
    rw [← hrho]
    have hmap :
        (doubleConeOtherBoundaryInclusion M).mapSimplex
            ((coneBottomInclusion M).mapSimplex rho) =
          (doubleConeInnerBoundaryInclusion M).mapSimplex
            ((coneBottomInclusion M).mapSimplex rho) := by
      exact (doubleConeFaces_mapSimplex_bottom_eq M n rho).symm
    rw [hmap, OrderedSimplicialMap.extendCochainByZero_apply_of_eq,
      OrderedSimplicialMap.extendCochainByZero_apply_of_eq,
      OrderedSimplicialMap.pullback_apply]

/-- Inclusion--exclusion gluing of compatible cochains on the two cone
faces. -/
def doubleConeBoundaryGluedCochain (n : ℕ)
    (cInner cOther : Cochain (simplicialCone M) n G) :
    Cochain (doubleConeBoundary M) n G :=
  (doubleConeInnerBoundaryInclusion M).extendCochainByZero n cInner +
    (doubleConeOtherBoundaryInclusion M).extendCochainByZero n
      (cOther - (coneBottomInclusion M).extendCochainByZero n
        ((coneBottomInclusion M).pullback n cInner))

/-- Gluing restricts to the prescribed inner cochain. -/
theorem inner_pullback_doubleConeBoundaryGluedCochain (n : ℕ)
    (cInner cOther : Cochain (simplicialCone M) n G)
    (hcompat : (coneBottomInclusion M).pullback n cInner =
      (coneBottomInclusion M).pullback n cOther) :
    (doubleConeInnerBoundaryInclusion M).pullback n
        (doubleConeBoundaryGluedCochain M n cInner cOther) = cInner := by
  rw [doubleConeBoundaryGluedCochain, map_add,
    OrderedSimplicialMap.pullback_extendCochainByZero,
    inner_pullback_other_extendCochainByZero, map_sub,
    OrderedSimplicialMap.pullback_extendCochainByZero, ← hcompat,
    sub_self, OrderedSimplicialMap.extendCochainByZero_zero, add_zero]

/-- Gluing restricts to the prescribed other-face cochain. -/
theorem other_pullback_doubleConeBoundaryGluedCochain (n : ℕ)
    (cInner cOther : Cochain (simplicialCone M) n G)
    (_hcompat : (coneBottomInclusion M).pullback n cInner =
      (coneBottomInclusion M).pullback n cOther) :
    (doubleConeOtherBoundaryInclusion M).pullback n
        (doubleConeBoundaryGluedCochain M n cInner cOther) = cOther := by
  rw [doubleConeBoundaryGluedCochain, map_add,
    other_pullback_inner_extendCochainByZero,
    OrderedSimplicialMap.pullback_extendCochainByZero]
  abel

/-- A cochain on the double-cone boundary is determined by its restrictions
to the two cone faces.  This is the cochain-level form of the literal cover
`C_vM ∪_M C_wM`. -/
theorem doubleConeBoundary_cochain_ext_two_faces (n : ℕ)
    {u v : Cochain (doubleConeBoundary M) n G}
    (hinner : (doubleConeInnerBoundaryInclusion M).pullback n u =
      (doubleConeInnerBoundaryInclusion M).pullback n v)
    (hother : (doubleConeOtherBoundaryInclusion M).pullback n u =
      (doubleConeOtherBoundaryInclusion M).pullback n v) :
    u = v := by
  ext tau
  let tauAmbient : Simplex (simplicialCone (simplicialCone M)) n :=
    ⟨tau.1, tau.2.1.1, tau.2.2⟩
  rcases tau.2.1.2 with houter | hinnerApex
  · rcases exists_coneBottom_simplex_of_apex_not_mem
        (simplicialCone M) n tauAmbient houter with ⟨sigma, hsigma⟩
    have hface :
        (doubleConeInnerBoundaryInclusion M).mapSimplex sigma = tau := by
      apply Subtype.ext
      change ((coneBottomInclusion (simplicialCone M)).mapSimplex sigma).1 =
        tauAmbient.1
      exact congrArg Subtype.val hsigma
    have hv := congrArg
      (fun c : Cochain (simplicialCone M) n G => c sigma) hinner
    change u ((doubleConeInnerBoundaryInclusion M).mapSimplex sigma) =
      v ((doubleConeInnerBoundaryInclusion M).mapSimplex sigma) at hv
    simpa [hface] using hv
  · rcases exists_doubleConeOther_simplex_of_inner_apex_not_mem
        M n tauAmbient hinnerApex with ⟨sigma, hsigma⟩
    have hface :
        (doubleConeOtherBoundaryInclusion M).mapSimplex sigma = tau := by
      simpa [tauAmbient] using hsigma
    have hv := congrArg
      (fun c : Cochain (simplicialCone M) n G => c sigma) hother
    change u ((doubleConeOtherBoundaryInclusion M).mapSimplex sigma) =
      v ((doubleConeOtherBoundaryInclusion M).mapSimplex sigma) at hv
    simpa [hface] using hv

/-! ## The first relative extension, from one face to the boundary -/

/-- Extend a cochain on the inner cone across the boundary.  Its value on
the other cone is supplied by the chosen fibrewise extension of its bottom
restriction. -/
def doubleConeBoundaryCochainLift (n : ℕ)
    (Q : FiberwiseCochainLift
      (coboundaryToRange (G := G) M n)
      (coboundaryToRange (G := G) (simplicialCone M) n)
      (coneBottomFacetHom (G := G) M n).primitiveMap)
    (c : Cochain (simplicialCone M) n G) :
    Cochain (doubleConeBoundary M) n G :=
  doubleConeBoundaryGluedCochain M n c
    (Q.lift ((coneBottomInclusion M).pullback n c))

@[simp]
theorem inner_pullback_doubleConeBoundaryCochainLift (n : ℕ)
    (Q : FiberwiseCochainLift
      (coboundaryToRange (G := G) M n)
      (coboundaryToRange (G := G) (simplicialCone M) n)
      (coneBottomFacetHom (G := G) M n).primitiveMap)
    (c : Cochain (simplicialCone M) n G) :
    (doubleConeInnerBoundaryInclusion M).pullback n
        (doubleConeBoundaryCochainLift M n Q c) = c := by
  apply inner_pullback_doubleConeBoundaryGluedCochain
  symm
  exact Q.res_lift ((coneBottomInclusion M).pullback n c)

@[simp]
theorem other_pullback_doubleConeBoundaryCochainLift (n : ℕ)
    (Q : FiberwiseCochainLift
      (coboundaryToRange (G := G) M n)
      (coboundaryToRange (G := G) (simplicialCone M) n)
      (coneBottomFacetHom (G := G) M n).primitiveMap)
    (c : Cochain (simplicialCone M) n G) :
    (doubleConeOtherBoundaryInclusion M).pullback n
        (doubleConeBoundaryCochainLift M n Q c) =
      Q.lift ((coneBottomInclusion M).pullback n c) := by
  apply other_pullback_doubleConeBoundaryGluedCochain
  symm
  exact Q.res_lift ((coneBottomInclusion M).pullback n c)

/-- The coboundary of the glued lift depends only on the coboundary of the
inner-face cochain.  This is the fibrewise property needed to send a
primitive relation to a primitive relation. -/
theorem coboundary_doubleConeBoundaryCochainLift_eq_of_eq (n : ℕ)
    (Q : FiberwiseCochainLift
      (coboundaryToRange (G := G) M n)
      (coboundaryToRange (G := G) (simplicialCone M) n)
      (coneBottomFacetHom (G := G) M n).primitiveMap)
    (c c' : Cochain (simplicialCone M) n G)
    (hcc' : coboundary (simplicialCone M) n c =
      coboundary (simplicialCone M) n c') :
    coboundary (doubleConeBoundary M) n
        (doubleConeBoundaryCochainLift M n Q c) =
      coboundary (doubleConeBoundary M) n
        (doubleConeBoundaryCochainLift M n Q c') := by
  apply doubleConeBoundary_cochain_ext_two_faces M (n + 1)
  · calc
      (doubleConeInnerBoundaryInclusion M).pullback (n + 1)
          (coboundary (doubleConeBoundary M) n
            (doubleConeBoundaryCochainLift M n Q c)) =
          coboundary (simplicialCone M) n
            ((doubleConeInnerBoundaryInclusion M).pullback n
              (doubleConeBoundaryCochainLift M n Q c)) :=
        LinearMap.congr_fun
          ((doubleConeInnerBoundaryInclusion M).pullback_coboundary
            (G := G) n)
          (doubleConeBoundaryCochainLift M n Q c)
      _ = coboundary (simplicialCone M) n c := by
        rw [inner_pullback_doubleConeBoundaryCochainLift]
      _ = coboundary (simplicialCone M) n c' := hcc'
      _ = coboundary (simplicialCone M) n
            ((doubleConeInnerBoundaryInclusion M).pullback n
              (doubleConeBoundaryCochainLift M n Q c')) := by
        rw [inner_pullback_doubleConeBoundaryCochainLift]
      _ = (doubleConeInnerBoundaryInclusion M).pullback (n + 1)
          (coboundary (doubleConeBoundary M) n
            (doubleConeBoundaryCochainLift M n Q c')) :=
        (LinearMap.congr_fun
          ((doubleConeInnerBoundaryInclusion M).pullback_coboundary
            (G := G) n)
          (doubleConeBoundaryCochainLift M n Q c')).symm
  · have hbottomCoboundary :
        coboundary M n ((coneBottomInclusion M).pullback n c) =
          coboundary M n ((coneBottomInclusion M).pullback n c') := by
      calc
        coboundary M n ((coneBottomInclusion M).pullback n c) =
            (coneBottomInclusion M).pullback (n + 1)
              (coboundary (simplicialCone M) n c) :=
          (LinearMap.congr_fun
            ((coneBottomInclusion M).pullback_coboundary (G := G) n) c).symm
        _ = (coneBottomInclusion M).pullback (n + 1)
              (coboundary (simplicialCone M) n c') := by rw [hcc']
        _ = coboundary M n
              ((coneBottomInclusion M).pullback n c') :=
          LinearMap.congr_fun
            ((coneBottomInclusion M).pullback_coboundary (G := G) n) c'
    have hbottomRange :
        coboundaryToRange (G := G) M n
            ((coneBottomInclusion M).pullback n c) =
          coboundaryToRange (G := G) M n
            ((coneBottomInclusion M).pullback n c') := by
      apply Subtype.ext
      exact hbottomCoboundary
    calc
      (doubleConeOtherBoundaryInclusion M).pullback (n + 1)
          (coboundary (doubleConeBoundary M) n
            (doubleConeBoundaryCochainLift M n Q c)) =
          coboundary (simplicialCone M) n
            ((doubleConeOtherBoundaryInclusion M).pullback n
              (doubleConeBoundaryCochainLift M n Q c)) :=
        LinearMap.congr_fun
          ((doubleConeOtherBoundaryInclusion M).pullback_coboundary
            (G := G) n)
          (doubleConeBoundaryCochainLift M n Q c)
      _ = coboundary (simplicialCone M) n
            (Q.lift ((coneBottomInclusion M).pullback n c)) := by
        rw [other_pullback_doubleConeBoundaryCochainLift]
      _ = (Q.physicalLift
            (coboundaryToRange (G := G) M n
              ((coneBottomInclusion M).pullback n c))).1 := by
        exact congrArg Subtype.val
          (Q.d_lift ((coneBottomInclusion M).pullback n c))
      _ = (Q.physicalLift
            (coboundaryToRange (G := G) M n
              ((coneBottomInclusion M).pullback n c'))).1 := by
        rw [hbottomRange]
      _ = coboundary (simplicialCone M) n
            (Q.lift ((coneBottomInclusion M).pullback n c')) := by
        exact (congrArg Subtype.val
          (Q.d_lift ((coneBottomInclusion M).pullback n c'))).symm
      _ = coboundary (simplicialCone M) n
            ((doubleConeOtherBoundaryInclusion M).pullback n
              (doubleConeBoundaryCochainLift M n Q c')) := by
        rw [other_pullback_doubleConeBoundaryCochainLift]
      _ = (doubleConeOtherBoundaryInclusion M).pullback (n + 1)
          (coboundary (doubleConeBoundary M) n
            (doubleConeBoundaryCochainLift M n Q c')) :=
        (LinearMap.congr_fun
          ((doubleConeOtherBoundaryInclusion M).pullback_coboundary
            (G := G) n)
          (doubleConeBoundaryCochainLift M n Q c')).symm

/-- The glued cochain lift, packaged with its fibrewise coboundary
dependence.  This is the first of the two relative extensions in the
double-cone argument. -/
def innerFaceToDoubleConeBoundaryFiberwiseCochainLift (n : ℕ)
    (Q : FiberwiseCochainLift
      (coboundaryToRange (G := G) M n)
      (coboundaryToRange (G := G) (simplicialCone M) n)
      (coneBottomFacetHom (G := G) M n).primitiveMap) :
    FiberwiseCochainLift
      (coboundaryToRange (G := G) (simplicialCone M) n)
      (coboundaryToRange (G := G) (doubleConeBoundary M) n)
      ((doubleConeInnerBoundaryInclusion M).pullback
        (G := G) n).toAddMonoidHom where
  lift := doubleConeBoundaryCochainLift M n Q
  physicalLift b :=
    coboundaryToRange (G := G) (doubleConeBoundary M) n
      (doubleConeBoundaryCochainLift M n Q
        (chosenFiberRepresentative
          (coboundaryToRange_surjective
            (G := G) (simplicialCone M) n) b))
  res_lift c := inner_pullback_doubleConeBoundaryCochainLift M n Q c
  d_lift c := by
    apply Subtype.ext
    apply coboundary_doubleConeBoundaryCochainLift_eq_of_eq M n Q
    exact (congrArg Subtype.val
      (d_chosenFiberRepresentative
        (coboundaryToRange_surjective
          (G := G) (simplicialCone M) n)
        (coboundaryToRange (G := G) (simplicialCone M) n c))).symm

/-- The primitive relation denoted `r ∪ 0`: it is obtained by applying the
free reduced-distribution functor to the preceding glued fibrewise lift. -/
def primitiveRelationCupZero (n : ℕ)
    (Q : FiberwiseCochainLift
      (coboundaryToRange (G := G) M n)
      (coboundaryToRange (G := G) (simplicialCone M) n)
      (coneBottomFacetHom (G := G) M n).primitiveMap) :
    Rprim (d := coboundaryToRange (G := G) (simplicialCone M) n) →ₗ[ℤ]
      Rprim (d := coboundaryToRange (G := G) (doubleConeBoundary M) n) :=
  (innerFaceToDoubleConeBoundaryFiberwiseCochainLift M n Q).relationSection

/-- On the inner cone, `r ∪ 0` restricts strictly to `r`. -/
theorem inner_pullback_primitiveRelationCupZero (n : ℕ)
    (Q : FiberwiseCochainLift
      (coboundaryToRange (G := G) M n)
      (coboundaryToRange (G := G) (simplicialCone M) n)
      (coneBottomFacetHom (G := G) M n).primitiveMap)
    (r : Rprim
      (d := coboundaryToRange (G := G) (simplicialCone M) n)) :
    mapRedDist
        ((doubleConeInnerBoundaryInclusion M).pullback
          (G := G) n).toAddMonoidHom
        (primitiveRelationCupZero M n Q r).1 = r.1 := by
  exact FiberwiseCochainLift.mapRedDist_relationSection
    (innerFaceToDoubleConeBoundaryFiberwiseCochainLift M n Q) r

/-- If `r` is zero on the common bottom, then the other-cone restriction of
`r ∪ 0` is literally zero. -/
theorem other_pullback_primitiveRelationCupZero_eq_zero (n : ℕ)
    (Q : FiberwiseCochainLift
      (coboundaryToRange (G := G) M n)
      (coboundaryToRange (G := G) (simplicialCone M) n)
      (coneBottomFacetHom (G := G) M n).primitiveMap)
    (r : Rprim
      (d := coboundaryToRange (G := G) (simplicialCone M) n))
    (hr : coneBottomRprimRestriction (G := G) M n r = 0) :
    mapRedDist
        ((doubleConeOtherBoundaryInclusion M).pullback
          (G := G) n).toAddMonoidHom
        (primitiveRelationCupZero M n Q r).1 = 0 := by
  have hr' :
      mapRedDist
          ((coneBottomInclusion M).pullback
            (G := G) n).toAddMonoidHom r.1 = 0 := by
    exact congrArg Subtype.val hr
  rw [mapRedDist_eq_mapRedDistFn]
  change mapRedDistFn
      ((doubleConeOtherBoundaryInclusion M).pullback
        (G := G) n).toAddMonoidHom
      ((FiberwiseCochainLift.relationSection
        (innerFaceToDoubleConeBoundaryFiberwiseCochainLift M n Q) r).1) = 0
  rw [FiberwiseCochainLift.relationSection_coe]
  calc
    mapRedDistFn
        ((doubleConeOtherBoundaryInclusion M).pullback
          (G := G) n).toAddMonoidHom
        (mapRedDistFn (doubleConeBoundaryCochainLift M n Q) r.1) =
      mapRedDistFn
        (((doubleConeOtherBoundaryInclusion M).pullback
          (G := G) n) ∘ doubleConeBoundaryCochainLift M n Q) r.1 :=
      mapRedDistFn_comp_apply
        (doubleConeBoundaryCochainLift M n Q)
        ((doubleConeOtherBoundaryInclusion M).pullback
          (G := G) n).toAddMonoidHom r.1
    _ = mapRedDistFn
        (Q.lift ∘ (coneBottomInclusion M).pullback (G := G) n) r.1 := by
      have hfun :
          ((doubleConeOtherBoundaryInclusion M).pullback
              (G := G) n : Cochain (doubleConeBoundary M) n G →
                Cochain (simplicialCone M) n G) ∘
              doubleConeBoundaryCochainLift M n Q =
            Q.lift ∘ (coneBottomInclusion M).pullback (G := G) n := by
        funext c
        exact other_pullback_doubleConeBoundaryCochainLift M n Q c
      rw [hfun]
    _ = mapRedDistFn Q.lift
        (mapRedDistFn
          ((coneBottomInclusion M).pullback
            (G := G) n).toAddMonoidHom r.1) :=
      (mapRedDistFn_comp_apply
        ((coneBottomInclusion M).pullback
          (G := G) n).toAddMonoidHom Q.lift r.1).symm
    _ = mapRedDistFn Q.lift 0 := by
      rw [← mapRedDist_eq_mapRedDistFn, hr']
    _ = 0 := by simp

/-! ## The second relative extension, into the outer cone -/

/-- Extend `r ∪ 0` from the double-cone boundary to the whole outer cone.
The second fibrewise lift is supplied by the shifted relative-cohomology
vanishing theorem. -/
def outerConePrimitiveExtension (n : ℕ)
    (Q : FiberwiseCochainLift
      (coboundaryToRange (G := G) M n)
      (coboundaryToRange (G := G) (simplicialCone M) n)
      (coneBottomFacetHom (G := G) M n).primitiveMap)
    (S : FiberwiseCochainLift
      (coboundaryToRange (G := G) (doubleConeBoundary M) n)
      (coboundaryToRange (G := G)
        (simplicialCone (simplicialCone M)) n)
      ((doubleConeBoundaryInclusion M).pullback
        (G := G) n).toAddMonoidHom)
    (r : Rprim
      (d := coboundaryToRange (G := G) (simplicialCone M) n)) :
    Rprim (d := coboundaryToRange (G := G)
      (simplicialCone (simplicialCone M)) n) :=
  S.relationSection (primitiveRelationCupZero M n Q r)

/-- The outer extension restricts to exactly `r ∪ 0` on the literal
double-cone boundary. -/
theorem boundary_pullback_outerConePrimitiveExtension (n : ℕ)
    (Q : FiberwiseCochainLift
      (coboundaryToRange (G := G) M n)
      (coboundaryToRange (G := G) (simplicialCone M) n)
      (coneBottomFacetHom (G := G) M n).primitiveMap)
    (S : FiberwiseCochainLift
      (coboundaryToRange (G := G) (doubleConeBoundary M) n)
      (coboundaryToRange (G := G)
        (simplicialCone (simplicialCone M)) n)
      ((doubleConeBoundaryInclusion M).pullback
        (G := G) n).toAddMonoidHom)
    (r : Rprim
      (d := coboundaryToRange (G := G) (simplicialCone M) n)) :
    mapRedDist
        ((doubleConeBoundaryInclusion M).pullback
          (G := G) n).toAddMonoidHom
        (outerConePrimitiveExtension M n Q S r).1 =
      (primitiveRelationCupZero M n Q r).1 := by
  exact S.mapRedDist_relationSection (primitiveRelationCupZero M n Q r)

end GeneralSphereT.SimplicialCochain
