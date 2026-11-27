import Formalization.Section4PointedConePairCohomologyShift

set_option linter.style.header false

/-!
# Section 4: the second cohomological shift on the double cone

This file proves the relative-cochain input used in (4.17).  The ambient
complex is `C_w C_v M`, and its boundary is the literal union
`C_v M ∪_M C_w M` defined by `doubleConeBoundary`.

The proof contracts a relative cocycle in the outer cone.  Its restriction
to the inner cone is a relative cocycle for `M ⊆ C_v M`, so the one-cone
shift proved in `Section4PointedConePairCohomologyShift` supplies the one
correction that is needed.  The corrected primitive vanishes separately on
the two cone faces and hence on their union.
-/

noncomputable section

namespace GeneralSphereT.SimplicialCochain

variable {V G : Type*} [LinearOrder V] [Fintype V] [AddCommGroup G]
variable (M : AbstractSimplicialComplex V)

local instance (priority := 10000) doubleShiftOptionLE : LE (Option V) :=
  @WithBot.instLE V inferInstance

local instance (priority := 10000) doubleShiftOptionLT : LT (Option V) :=
  @WithBot.instLT V inferInstance

local instance (priority := 10000) doubleShiftOptionLinearOrder :
    LinearOrder (Option V) :=
  @WithBot.linearOrder V inferInstance

local instance (priority := 10001) doubleShiftOptionOptionLE :
    LE (Option (Option V)) :=
  @WithBot.instLE (Option V) inferInstance

local instance (priority := 10001) doubleShiftOptionOptionLT :
    LT (Option (Option V)) :=
  @WithBot.instLT (Option V) inferInstance

local instance (priority := 10001) doubleShiftOptionOptionLinearOrder :
    LinearOrder (Option (Option V)) :=
  @WithBot.linearOrder (Option V) inferInstance

/-! ## The two cone faces -/

/-- The inner cone `C_vM` as the bottom face of `C_wC_vM`, with codomain
restricted to the double-cone boundary. -/
def doubleConeInnerBoundaryInclusion :
    OrderedSimplicialMap (simplicialCone M) (doubleConeBoundary M) where
  toOrderEmbedding := coneBottomOrderEmbedding
  map_mem := by
    intro s hs
    rw [mem_doubleConeBoundary]
    refine ⟨(coneBottomInclusion (simplicialCone M)).map_mem hs, Or.inl ?_⟩
    intro hnone
    rcases Finset.mem_map.mp hnone with ⟨x, _hx, hx⟩
    exact Option.some_ne_none x hx

/-- The order embedding of the other cone face `C_wM`: it fixes the outer
apex and sends every old vertex to the twice-embedded bottom vertex. -/
def doubleConeOtherOrderEmbedding :
    Option V ↪o Option (Option V) :=
  coneBottomOrderEmbedding.withBotMap

@[simp]
theorem doubleConeOtherOrderEmbedding_none :
    doubleConeOtherOrderEmbedding (V := V) none = none :=
  rfl

@[simp]
theorem doubleConeOtherOrderEmbedding_some (v : V) :
    doubleConeOtherOrderEmbedding (V := V) (some v) = some (some v) :=
  rfl

/-- The evident partial inverse to the other-cone embedding.  Its only
failure to be a two-sided inverse is at the excluded inner apex
`some none`. -/
def doubleConeOtherRetraction : Option (Option V) → Option V
  | none => none
  | some o => o

@[simp]
theorem doubleConeOtherRetraction_none :
    doubleConeOtherRetraction (V := V) none = none :=
  rfl

@[simp]
theorem doubleConeOtherRetraction_some (o : Option V) :
    doubleConeOtherRetraction (V := V) (some o) = o :=
  rfl

@[simp]
theorem doubleConeOtherRetraction_embedding (o : Option V) :
    doubleConeOtherRetraction (V := V)
      (doubleConeOtherOrderEmbedding o) = o := by
  cases o <;> rfl

/-- The other cone `C_wM` as a subcomplex of the double-cone boundary. -/
def doubleConeOtherBoundaryInclusion :
    OrderedSimplicialMap (simplicialCone M) (doubleConeBoundary M) where
  toOrderEmbedding := doubleConeOtherOrderEmbedding
  map_mem := by
    intro s hs
    rw [mem_doubleConeBoundary]
    let t : Finset (Option (Option V)) :=
      s.map (doubleConeOtherOrderEmbedding (V := V)).toEmbedding
    have htne : t.Nonempty := Finset.map_nonempty.mpr
      ((simplicialCone M).isRelLowerSet_faces hs).1
    have hbase : coneBaseVertices t = s.erase none := by
      ext o
      cases o with
      | none =>
          rw [mem_coneBaseVertices]
          simp only [t, Finset.mem_map, Finset.mem_erase]
          constructor
          · rintro ⟨x, _hx, hx⟩
            change doubleConeOtherOrderEmbedding x = some none at hx
            cases x <;> simp at hx
          · rintro ⟨h, _⟩
            exact (h rfl).elim
      | some v =>
          rw [mem_coneBaseVertices]
          simp only [t, Finset.mem_map, Finset.mem_erase,
            Option.some.injEq]
          constructor
          · rintro ⟨x, hx, hmap⟩
            change doubleConeOtherOrderEmbedding x = some (some v) at hmap
            cases x with
            | none => simp at hmap
            | some w =>
                simp only [doubleConeOtherOrderEmbedding_some,
                  Option.some.injEq] at hmap
                subst w
                exact ⟨Option.some_ne_none v, hx⟩
          · rintro ⟨_ne, hv⟩
            exact ⟨some v, hv, by simp⟩
    refine ⟨?_, ?_⟩
    · rw [mem_simplicialCone, hbase]
      refine ⟨htne, ?_⟩
      by_cases hzero : s.erase none = ∅
      · exact Or.inl hzero
      · exact Or.inr ((simplicialCone M).isRelLowerSet_faces hs |>.2
          (Finset.erase_subset _ _) (Finset.nonempty_iff_ne_empty.mpr hzero))
    · right
      intro hinner
      rcases Finset.mem_map.mp hinner with ⟨o, _ho, ho⟩
      cases o with
      | none =>
          change doubleConeOtherOrderEmbedding none = some none at ho
          simp at ho
      | some v =>
          change doubleConeOtherOrderEmbedding (some v) = some none at ho
          simp at ho

/-- The other cone face regarded directly as a subcomplex of the ambient
double cone. -/
def doubleConeOtherInclusion :
    OrderedSimplicialMap (simplicialCone M)
      (simplicialCone (simplicialCone M)) :=
  OrderedSimplicialMap.comp (doubleConeBoundaryInclusion M)
    (doubleConeOtherBoundaryInclusion M)

/-! ## Elementary simplex classification -/

/-- A simplex of a literal cone which avoids its apex comes uniquely from
the bottom.  This is the unpointed version of the elementary classification
used for the pointed cone pair. -/
theorem exists_coneBottom_simplex_of_apex_not_mem
    (X : AbstractSimplicialComplex V) (n : ℕ)
    (tau : Simplex (simplicialCone X) n)
    (htau : (none : Option V) ∉ tau.1) :
    ∃ sigma : Simplex X n, (coneBottomInclusion X).mapSimplex sigma = tau := by
  let s : Finset V := coneBaseVertices tau.1
  have himage : s.image some = tau.1 := by
    ext o
    cases o with
    | none => simp [htau]
    | some x => simp [s, mem_coneBaseVertices]
  have hsne : s.Nonempty := by
    have htne : tau.1.Nonempty :=
      ((simplicialCone X).isRelLowerSet_faces tau.2.1).1
    rcases htne with ⟨o, ho⟩
    cases o with
    | none => exact (htau ho).elim
    | some x => exact ⟨x, (mem_coneBaseVertices tau.1 x).mpr ho⟩
  have hsX : s ∈ X := by
    rcases (mem_simplicialCone X tau.1).mp tau.2.1 |>.2 with hs0 | hsX
    · exact (Finset.Nonempty.ne_empty hsne hs0).elim
    · exact hsX
  have hcard : s.card = n + 1 := by
    calc
      s.card = (s.image some).card :=
        (Finset.card_image_of_injective s (Option.some_injective V)).symm
      _ = tau.1.card := congrArg Finset.card himage
      _ = n + 1 := tau.2.2
  let sigma : Simplex X n := ⟨s, hsX, hcard⟩
  refine ⟨sigma, ?_⟩
  apply Subtype.ext
  change s.map coneBottomOrderEmbedding.toEmbedding = tau.1
  calc
    s.map coneBottomOrderEmbedding.toEmbedding = s.image some := by
      rw [Finset.map_eq_image]
      congr 1
    _ = tau.1 := himage

/-- Every simplex of `C_wC_vM` which avoids the inner apex belongs to the
other cone face `C_wM`. -/
theorem exists_doubleConeOther_simplex_of_inner_apex_not_mem (n : ℕ)
    (tau : Simplex (simplicialCone (simplicialCone M)) n)
    (htau : (some none : Option (Option V)) ∉ tau.1) :
    ∃ sigma : Simplex (simplicialCone M) n,
      (doubleConeOtherBoundaryInclusion M).mapSimplex sigma =
        ⟨tau.1, ⟨tau.2.1, Or.inr htau⟩, tau.2.2⟩ := by
  let s : Finset (Option V) :=
    tau.1.image (doubleConeOtherRetraction (V := V))
  have himage :
      s.map (doubleConeOtherOrderEmbedding (V := V)).toEmbedding = tau.1 := by
    ext o
    constructor
    · intro ho
      rcases Finset.mem_map.mp ho with ⟨x, hx, hxo⟩
      rcases Finset.mem_image.mp hx with ⟨y, hy, hyx⟩
      subst x
      cases y with
      | none => simpa using hxo ▸ hy
      | some y =>
          cases y with
          | none =>
              exfalso
              exact htau hy
          | some v =>
              simpa using hxo ▸ hy
    · intro ho
      refine Finset.mem_map.mpr
        ⟨doubleConeOtherRetraction (V := V) o, ?_, ?_⟩
      · exact Finset.mem_image.mpr ⟨o, ho, rfl⟩
      · cases o with
        | none => rfl
        | some o =>
            cases o with
            | none => exact (htau ho).elim
            | some v => rfl
  have hsne : s.Nonempty := Finset.image_nonempty.mpr
    ((simplicialCone (simplicialCone M)).isRelLowerSet_faces tau.2.1).1
  have hbase :
      coneBaseVertices s = coneBaseVertices (coneBaseVertices tau.1) := by
    ext v
    rw [mem_coneBaseVertices, mem_coneBaseVertices]
    constructor
    · intro hv
      rcases Finset.mem_image.mp hv with ⟨o, ho, hov⟩
      cases o with
      | none => simp at hov
      | some o =>
          simp only [doubleConeOtherRetraction_some] at hov
          subst o
          exact (mem_coneBaseVertices tau.1 (some v)).mpr ho
    · intro hv
      exact Finset.mem_image.mpr
        ⟨some (some v), (mem_coneBaseVertices tau.1 (some v)).mp hv, rfl⟩
  have hsface : s ∈ simplicialCone M := by
    rw [mem_simplicialCone, hbase]
    refine ⟨hsne, ?_⟩
    rcases (mem_simplicialCone (simplicialCone M) tau.1).mp tau.2.1 |>.2 with
      houterZero | houterFace
    · left
      rw [houterZero]
      ext v
      simp [mem_coneBaseVertices]
    · exact (mem_simplicialCone M (coneBaseVertices tau.1)).mp
        houterFace |>.2
  have hcard : s.card = n + 1 := by
    calc
      s.card =
          (s.map (doubleConeOtherOrderEmbedding (V := V)).toEmbedding).card :=
        (Finset.card_map _).symm
      _ = tau.1.card := congrArg Finset.card himage
      _ = n + 1 := tau.2.2
  let sigma : Simplex (simplicialCone M) n := ⟨s, hsface, hcard⟩
  refine ⟨sigma, ?_⟩
  apply Subtype.ext
  exact himage

/-! ## The outer contraction is zero on the other cone face -/

/-- A relative cochain for the identity inclusion of the boundary vanishes
pointwise on every ambient simplex whose vertex set is a boundary face. -/
theorem doubleConeRelativeCochain_apply_of_mem (n : ℕ)
    (c : (doubleConeBoundaryInclusion M).RelativeCochain (G := G) n)
    (tau : Simplex (simplicialCone (simplicialCone M)) n)
    (htau : tau.1 ∈ doubleConeBoundary M) :
    c.1 tau = 0 := by
  let tauBoundary : Simplex (doubleConeBoundary M) n :=
    ⟨tau.1, htau, tau.2.2⟩
  have hc := congrArg
    (fun z : Cochain (doubleConeBoundary M) n G => z tauBoundary) c.2
  have hmap :
      (doubleConeBoundaryInclusion M).mapSimplex tauBoundary = tau := by
    apply Subtype.ext
    simp [tauBoundary, doubleConeBoundaryInclusion,
      OrderedSimplicialMap.mapSimplex]
  change c.1 ((doubleConeBoundaryInclusion M).mapSimplex tauBoundary) = 0 at hc
  simpa [hmap] using hc

/-- Contracting in the outer cone sends a double-cone relative cochain to
zero on every simplex which avoids the inner apex.  If the simplex contains
the outer apex this is the normalization of the cone homotopy; otherwise the
inserted outer cone simplex lies in the other boundary face. -/
theorem doubleConeOuterPrimitive_zero_of_inner_apex_not_mem (n : ℕ)
    (gamma : (doubleConeBoundaryInclusion M).RelativeCochain
      (G := G) (n + 1))
    (sigma : Simplex (simplicialCone (simplicialCone M)) n)
    (hinner : (some none : Option (Option V)) ∉ sigma.1) :
    simplicialConeCocyclePrimitive (simplicialCone M) n gamma.1 sigma = 0 := by
  by_cases houter : (none : Option (Option V)) ∈ sigma.1
  · exact simplicialConeCocyclePrimitive_apexFree
      (G := G) (simplicialCone M) n gamma.1 sigma houter
  · let sigmaStar : ClosedStarSimplex
        (simplicialCone (simplicialCone M))
        (coneApexSimplex (simplicialCone (simplicialCone M)) none) n :=
      ⟨sigma, simplex_mem_apexClosedStar
        (simplicialCone (simplicialCone M))
        (simplicialCone_isConeAt (simplicialCone M)) sigma⟩
    let inserted := insertClosedStarVertex
      (simplicialCone (simplicialCone M)) none
      (mem_coneApexSimplex (simplicialCone (simplicialCone M)) none)
      sigmaStar houter
    have hinserted : inserted.1.1 ∈ doubleConeBoundary M := by
      rw [mem_doubleConeBoundary]
      refine ⟨inserted.1.2.1, Or.inr ?_⟩
      intro h
      change (some none : Option (Option V)) ∈
        insert (none : Option (Option V)) sigma.1 at h
      rcases Finset.mem_insert.mp h with hEq | hmem
      · exact Option.some_ne_none none hEq
      · exact hinner hmem
    have hgamma : gamma.1 inserted.1 = 0 :=
      doubleConeRelativeCochain_apply_of_mem
        (G := G) M (n + 1) gamma inserted.1 hinserted
    let apex := coneApexSimplex
      (simplicialCone (simplicialCone M)) none
    calc
      simplicialConeCocyclePrimitive (simplicialCone M) n gamma.1 sigma =
          restrictClosedStar (simplicialCone (simplicialCone M)) apex n
            (simplicialConeCocyclePrimitive
              (simplicialCone M) n gamma.1) sigmaStar := rfl
      _ = coneHomotopy (simplicialCone (simplicialCone M)) apex none
            (mem_coneApexSimplex
              (simplicialCone (simplicialCone M)) none) n
            (restrictClosedStar (simplicialCone (simplicialCone M)) apex
              (n + 1) gamma.1) sigmaStar := by
        rw [simplicialConeCocyclePrimitive,
          restrictClosedStar_extendCarrierClosedStar]
      _ = incidenceSign (simplicialCone (simplicialCone M)) inserted.1 none •
            restrictClosedStar (simplicialCone (simplicialCone M)) apex
              (n + 1) gamma.1 inserted := by
        exact coneHomotopy_apply_of_not_mem
          (simplicialCone (simplicialCone M)) apex none
          (mem_coneApexSimplex
            (simplicialCone (simplicialCone M)) none) n _ sigmaStar houter
      _ = 0 := by
        rw [restrictClosedStar_apply, hgamma, smul_zero]

/-! ## The correction extended from the inner cone -/

/-- A relative cochain on `(C_vM,M)`, extended by zero from `C_vM` to the
outer cone, restricts to zero on the other cone face `C_wM`. -/
theorem doubleConeOther_pullback_outerBottomExtension_eq_zero (n : ℕ)
    (p : (coneBottomInclusion M).RelativeCochain (G := G) n) :
    (doubleConeOtherInclusion M).pullback n
        ((coneBottomInclusion (simplicialCone M)).extendCochainByZero n p.1) =
      0 := by
  let E := coneBottomInclusion (simplicialCone M)
  let J := doubleConeOtherInclusion M
  ext sigma
  rw [OrderedSimplicialMap.pullback_apply]
  by_cases houter : (none : Option V) ∈ sigma.1
  · apply OrderedSimplicialMap.extendCochainByZero_apply_of_not_mem_range
    rintro ⟨tau, htau⟩
    have hnoneJ : (none : Option (Option V)) ∈ (J.mapSimplex sigma).1 := by
      change (none : Option (Option V)) ∈
        sigma.1.map
          (doubleConeOtherOrderEmbedding (V := V)).toEmbedding
      exact Finset.mem_map.mpr ⟨none, houter, rfl⟩
    rw [← htau] at hnoneJ
    change (none : Option (Option V)) ∈
      tau.1.map coneBottomOrderEmbedding.toEmbedding at hnoneJ
    rcases Finset.mem_map.mp hnoneJ with ⟨x, _hx, hx⟩
    exact Option.some_ne_none x hx
  · rcases exists_coneBottom_simplex_of_apex_not_mem M n sigma houter with
      ⟨rho, hrho⟩
    have hmap :
        J.mapSimplex sigma = E.mapSimplex
          ((coneBottomInclusion M).mapSimplex rho) := by
      rw [← hrho]
      apply Subtype.ext
      ext o
      simp only [OrderedSimplicialMap.mapSimplex_val, Finset.mem_map]
      constructor
      · rintro ⟨v, hv, hvo⟩
        rcases hv with ⟨w, hw, hwv⟩
        change some w = v at hwv
        subst v
        refine ⟨some w, ⟨w, hw, rfl⟩, ?_⟩
        dsimp [J, E, doubleConeOtherInclusion,
          doubleConeOtherBoundaryInclusion, doubleConeBoundaryInclusion,
          doubleConeOtherOrderEmbedding, coneBottomInclusion,
          coneBottomOrderEmbedding] at hvo ⊢
        change some (some w) = o at hvo ⊢
        exact hvo
      · rintro ⟨v, hv, hvo⟩
        rcases hv with ⟨w, hw, hwv⟩
        change some w = v at hwv
        subst v
        refine ⟨some w, ⟨w, hw, rfl⟩, ?_⟩
        dsimp [J, E, doubleConeOtherInclusion,
          doubleConeOtherBoundaryInclusion, doubleConeBoundaryInclusion,
          doubleConeOtherOrderEmbedding, coneBottomInclusion,
          coneBottomOrderEmbedding] at hvo ⊢
        change some (some w) = o at hvo ⊢
        exact hvo
    rw [hmap, OrderedSimplicialMap.extendCochainByZero_apply_of_eq]
    have hp := congrArg (fun c : Cochain M n G => c rho) p.2
    change p.1 ((coneBottomInclusion M).mapSimplex rho) = 0 at hp
    exact hp

/-- The outer cone primitive itself restricts to zero on the other cone
face. -/
theorem doubleConeOther_pullback_outerPrimitive_eq_zero (n : ℕ)
    (gamma : (doubleConeBoundaryInclusion M).RelativeCochain
      (G := G) (n + 1)) :
    (doubleConeOtherInclusion M).pullback n
        (simplicialConeCocyclePrimitive
          (simplicialCone M) n gamma.1) = 0 := by
  ext sigma
  rw [OrderedSimplicialMap.pullback_apply]
  apply doubleConeOuterPrimitive_zero_of_inner_apex_not_mem
    (G := G) M n gamma
  intro hinner
  change (some none : Option (Option V)) ∈
    sigma.1.map
      (doubleConeOtherOrderEmbedding (V := V)).toEmbedding at hinner
  rcases Finset.mem_map.mp hinner with ⟨o, _ho, ho⟩
  cases o with
  | none =>
      change doubleConeOtherOrderEmbedding none = some none at ho
      simp at ho
  | some v =>
      change doubleConeOtherOrderEmbedding (some v) = some none at ho
      simp at ho

/-! ## Covering the double-cone boundary -/

/-- Restriction of a double-cone relative cochain to the inner cone is zero.
This is just the fact that the inner cone is one of the two boundary faces. -/
theorem doubleConeInner_pullback_relativeCochain_eq_zero (n : ℕ)
    (gamma : (doubleConeBoundaryInclusion M).RelativeCochain (G := G) n) :
    (coneBottomInclusion (simplicialCone M)).pullback n gamma.1 = 0 := by
  ext sigma
  rw [OrderedSimplicialMap.pullback_apply]
  apply doubleConeRelativeCochain_apply_of_mem (G := G) M n gamma
  rw [mem_doubleConeBoundary]
  refine ⟨(coneBottomInclusion (simplicialCone M)).map_mem sigma.2.1,
    Or.inl ?_⟩
  intro houter
  change (none : Option (Option V)) ∈
    sigma.1.map coneBottomOrderEmbedding.toEmbedding at houter
  rcases Finset.mem_map.mp houter with ⟨o, _ho, ho⟩
  exact Option.some_ne_none o ho

/-- The two literal cone faces cover `doubleConeBoundary`.  Consequently a
cochain which vanishes on both faces vanishes on the whole boundary. -/
theorem doubleConeBoundary_pullback_eq_zero_of_two_faces (n : ℕ)
    (u : Cochain (simplicialCone (simplicialCone M)) n G)
    (hinner :
      (coneBottomInclusion (simplicialCone M)).pullback n u = 0)
    (hother : (doubleConeOtherInclusion M).pullback n u = 0) :
    (doubleConeBoundaryInclusion M).pullback n u = 0 := by
  let F := doubleConeBoundaryInclusion M
  let E := coneBottomInclusion (simplicialCone M)
  let J := doubleConeOtherInclusion M
  ext tau
  rw [OrderedSimplicialMap.pullback_apply]
  let tauAmbient : Simplex (simplicialCone (simplicialCone M)) n :=
    F.mapSimplex tau
  rcases tau.2.1.2 with houter | hinnerApex
  · have houterAmbient :
        (none : Option (Option V)) ∉ tauAmbient.1 := by
      simpa [tauAmbient, F, doubleConeBoundaryInclusion,
        OrderedSimplicialMap.mapSimplex] using houter
    rcases exists_coneBottom_simplex_of_apex_not_mem
        (simplicialCone M) n tauAmbient houterAmbient with
      ⟨sigma, hsigma⟩
    have hv := congrArg
      (fun c : Cochain (simplicialCone M) n G => c sigma) hinner
    change u (E.mapSimplex sigma) = 0 at hv
    change u tauAmbient = 0
    rw [← hsigma]
    exact hv
  · have hinnerAmbient :
        (some none : Option (Option V)) ∉ tauAmbient.1 := by
      simpa [tauAmbient, F, doubleConeBoundaryInclusion,
        OrderedSimplicialMap.mapSimplex] using hinnerApex
    rcases exists_doubleConeOther_simplex_of_inner_apex_not_mem
        M n tauAmbient hinnerAmbient with ⟨sigma, hsigma⟩
    have hmap : J.mapSimplex sigma = tauAmbient := by
      rw [show J.mapSimplex sigma =
          F.mapSimplex ((doubleConeOtherBoundaryInclusion M).mapSimplex sigma) by
        exact OrderedSimplicialMap.mapSimplex_comp F
          (doubleConeOtherBoundaryInclusion M) sigma]
      rw [hsigma]
      apply Subtype.ext
      simp [F, doubleConeBoundaryInclusion,
        OrderedSimplicialMap.mapSimplex]
    have hv := congrArg
      (fun c : Cochain (simplicialCone M) n G => c sigma) hother
    change u (J.mapSimplex sigma) = 0 at hv
    change u tauAmbient = 0
    rw [← hmap]
    exact hv

/-! ## The second relative shift -/

/-- The vanishing consequence of the double-cone shift

`H^{n+2}(C_wC_vM, C_vM ∪_M C_wM; G) ≅ H̃^n(M;G)`.

This is exactly the relative-cohomology input for the second extension in
(4.17). -/
theorem doubleConeBoundaryRelativeCohomologyZero_of_reduced
    (b : V) (n : ℕ)
    (hred : ReducedCohomologyZeroAt (G := G) M b n) :
    (doubleConeBoundaryInclusion M).RelativeCohomologyZeroAtSucc
      (G := G) (n + 1) := by
  let F := doubleConeBoundaryInclusion M
  let E := coneBottomInclusion (simplicialCone M)
  let B := coneBottomInclusion M
  let J := doubleConeOtherInclusion M
  apply le_antisymm
  · rintro y ⟨x, rfl⟩
    rw [LinearMap.mem_ker]
    exact F.relativeCoboundary_relativeCoboundary (G := G) (n + 1) x
  · intro gamma hgammaKer
    rw [LinearMap.mem_ker] at hgammaKer
    have hgammaCycle :
        coboundary (simplicialCone (simplicialCone M)) (n + 2) gamma.1 = 0 :=
      congrArg Subtype.val hgammaKer
    let a : Cochain (simplicialCone (simplicialCone M)) (n + 1) G :=
      simplicialConeCocyclePrimitive (simplicialCone M) (n + 1) gamma.1
    have hda :
        coboundary (simplicialCone (simplicialCone M)) (n + 1) a =
          gamma.1 :=
      coboundary_simplicialConeCocyclePrimitive
        (G := G) (simplicialCone M) (n + 1) gamma.1 hgammaCycle
    let c : Cochain (simplicialCone M) (n + 1) G :=
      E.pullback (n + 1) a
    have hEgamma : E.pullback (n + 2) gamma.1 = 0 :=
      doubleConeInner_pullback_relativeCochain_eq_zero
        (G := G) M (n + 2) gamma
    have hcocycle :
        coboundary (simplicialCone M) (n + 1) c = 0 := by
      have hnat := LinearMap.congr_fun
        (E.pullback_coboundary (G := G) (n + 1)) a
      simp only [LinearMap.comp_apply] at hnat
      rw [← hnat, hda, hEgamma]
    have hcBottom : B.pullback (n + 1) c = 0 := by
      ext sigma
      simp only [c, OrderedSimplicialMap.pullback_apply]
      apply doubleConeOuterPrimitive_zero_of_inner_apex_not_mem
        (G := G) M (n + 1) gamma
      intro hinner
      change (some none : Option (Option V)) ∈
        ((B.mapSimplex sigma).1.map
          coneBottomOrderEmbedding.toEmbedding) at hinner
      rcases Finset.mem_map.mp hinner with ⟨o, ho, hsome⟩
      have hoNone : o = none := by
        change some o = some none at hsome
        simpa using hsome
      subst o
      change (none : Option V) ∈
        sigma.1.map coneBottomOrderEmbedding.toEmbedding at ho
      rcases Finset.mem_map.mp ho with ⟨v, _hv, hv⟩
      exact Option.some_ne_none v hv
    let cRelative : B.RelativeCochain (G := G) (n + 1) :=
      ⟨c, hcBottom⟩
    have hcRelativeCycle :
        B.relativeCoboundary (G := G) (n + 1) cRelative = 0 := by
      apply Subtype.ext
      exact hcocycle
    have hcRelativeKer : cRelative ∈ LinearMap.ker
        (B.relativeCoboundary (G := G) (n + 1)) :=
      hcRelativeCycle
    have hbottomRelative := coneBottomRelativeCohomologyZero_of_reduced
      (G := G) M b n hred
    rw [← hbottomRelative] at hcRelativeKer
    rcases hcRelativeKer with ⟨p, hp⟩
    have hdp : coboundary (simplicialCone M) n p.1 = c :=
      congrArg Subtype.val hp
    let z : Cochain (simplicialCone (simplicialCone M)) n G :=
      E.extendCochainByZero n p.1
    let u : Cochain (simplicialCone (simplicialCone M)) (n + 1) G :=
      a - coboundary (simplicialCone (simplicialCone M)) n z
    have hinnerU : E.pullback (n + 1) u = 0 := by
      change E.pullback (n + 1)
        (a - coboundary (simplicialCone (simplicialCone M)) n z) = 0
      rw [map_sub]
      have hnat := LinearMap.congr_fun
        (E.pullback_coboundary (G := G) n) z
      simp only [LinearMap.comp_apply] at hnat
      rw [hnat, show E.pullback (n + 1) a = c by rfl,
        show E.pullback n z = p.1 by
          exact E.pullback_extendCochainByZero n p.1,
        hdp, sub_self]
    have hotherU : J.pullback (n + 1) u = 0 := by
      change J.pullback (n + 1)
        (a - coboundary (simplicialCone (simplicialCone M)) n z) = 0
      rw [map_sub]
      have haOther : J.pullback (n + 1) a = 0 :=
        doubleConeOther_pullback_outerPrimitive_eq_zero
          (G := G) M (n + 1) gamma
      have hnat := LinearMap.congr_fun
        (J.pullback_coboundary (G := G) n) z
      simp only [LinearMap.comp_apply] at hnat
      have hzOther : J.pullback n z = 0 :=
        doubleConeOther_pullback_outerBottomExtension_eq_zero
          (G := G) M n p
      rw [haOther, hnat, hzOther, map_zero, sub_zero]
    let uRelative : F.RelativeCochain (G := G) (n + 1) :=
      ⟨u, by
        rw [LinearMap.mem_ker]
        exact doubleConeBoundary_pullback_eq_zero_of_two_faces
          (G := G) M (n + 1) u hinnerU hotherU⟩
    refine ⟨uRelative, ?_⟩
    apply Subtype.ext
    change coboundary (simplicialCone (simplicialCone M)) (n + 1)
      (a - coboundary (simplicialCone (simplicialCone M)) n z) = gamma.1
    rw [map_sub, hda, coboundary_coboundary, sub_zero]

/-- The chosen fibrewise cochain lift for the double-cone boundary
inclusion, constructed directly from reduced cohomology vanishing. -/
def doubleConeBoundaryFiberwiseCochainLiftOfReducedCohomology
    (b : V) (n : ℕ)
    (hred : ReducedCohomologyZeroAt (G := G) M b n) :=
  (doubleConeBoundaryInclusion M).fiberwiseCochainLiftOfRelativeCohomology
    (n + 1)
    (doubleConeBoundaryRelativeCohomologyZero_of_reduced
      (G := G) M b n hred)

/-- The two exactness inputs in (4.16--4.17), at their actual common
extension degree.  Reduced vanishing in degrees `n+1` and `n` gives,
respectively, the bottom-pair and double-cone-pair statements in relative
degree `n+2`. -/
theorem coneBottomAndDoubleConeRelativeCohomologyZero_two_shifts
    (b : V) (n : ℕ)
    (hhigh : ReducedCohomologyZeroAt (G := G) M b (n + 1))
    (hlow : ReducedCohomologyZeroAt (G := G) M b n) :
    (coneBottomInclusion M).RelativeCohomologyZeroAtSucc
        (G := G) (n + 1) ∧
      (doubleConeBoundaryInclusion M).RelativeCohomologyZeroAtSucc
        (G := G) (n + 1) :=
  ⟨coneBottomRelativeCohomologyZero_of_reduced
      (G := G) M b (n + 1) hhigh,
    doubleConeBoundaryRelativeCohomologyZero_of_reduced
      (G := G) M b n hlow⟩

/-- The two chosen fibrewise cochain lifts used by the successive
extensions in (4.16--4.17). -/
def coneBottomAndDoubleConeFiberwiseCochainLifts
    (b : V) (n : ℕ)
    (hhigh : ReducedCohomologyZeroAt (G := G) M b (n + 1))
    (hlow : ReducedCohomologyZeroAt (G := G) M b n) :=
  (coneBottomFiberwiseCochainLiftOfReducedCohomology
      (G := G) M b (n + 1) hhigh,
    doubleConeBoundaryFiberwiseCochainLiftOfReducedCohomology
      (G := G) M b n hlow)

end GeneralSphereT.SimplicialCochain
