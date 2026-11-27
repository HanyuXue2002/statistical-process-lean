import Formalization.Section4PointedConePairExtension

set_option linter.style.header false

/-!
# Section 4: the cohomological shift for the pointed cone pair

This file proves the cochain content of (4.10).  Reduced cohomology is
represented by the based cochain complex: in degree zero we take cochains
vanishing at the chosen vertex, while in positive degrees this is the usual
simplicial cochain complex.  Its vanishing condition is stated literally as
`range d = ker d` (with zero range in degree zero).

For the pair `M ∪ C_v{b} ⊆ C_vM`, a relative cocycle is first contracted
on the ambient cone.  The restriction of the resulting primitive to `M` is
a cocycle.  Reduced exactness makes that restriction a coboundary; subtracting
the coboundary of its pointed-pair extension makes the primitive relative.
This is the elementary cochain proof of

`H^{n+1}(C_vM, M ∪ C_v{b}; G) ≅ H̃^n(M;G)`

at the only consequence used in the paper, namely vanishing.
-/

noncomputable section

namespace GeneralSphereT.SimplicialCochain

open GeneralSphereT.PathAlgebra

variable {V G : Type*} [LinearOrder V] [Fintype V] [AddCommGroup G]
variable (M : AbstractSimplicialComplex V)

local instance (priority := 10000) cohomologyShiftOptionLE : LE (Option V) :=
  @WithBot.instLE V inferInstance

local instance (priority := 10000) cohomologyShiftOptionLT : LT (Option V) :=
  @WithBot.instLT V inferInstance

local instance (priority := 10000) cohomologyShiftOptionLinearOrder :
    LinearOrder (Option V) :=
  @WithBot.linearOrder V inferInstance

local instance (priority := 10001) cohomologyShiftOptionOptionLE :
    LE (Option (Option V)) :=
  @WithBot.instLE (Option V) inferInstance

local instance (priority := 10001) cohomologyShiftOptionOptionLT :
    LT (Option (Option V)) :=
  @WithBot.instLT (Option V) inferInstance

local instance (priority := 10001) cohomologyShiftOptionOptionLinearOrder :
    LinearOrder (Option (Option V)) :=
  @WithBot.linearOrder (Option V) inferInstance

/-! ## Reduced cohomology as a range--kernel condition -/

/-- Degree-zero cochains normalized at the chosen basepoint. -/
def BasedZeroCochain (b : V) : Submodule ℤ (Cochain M 0 G) :=
  LinearMap.ker
    (Finsupp.lapply (R := ℤ) (M := G) (basepointSimplex M b))

/-- The first differential of the based (reduced) cochain complex. -/
def basedZeroCoboundary (b : V) :
    BasedZeroCochain (G := G) M b →ₗ[ℤ] Cochain M 1 G :=
  (coboundary M 0).comp (BasedZeroCochain (G := G) M b).subtype

/-- Vanishing of `H̃^n(M;G)`, written only as exactness of cochains.

In degree zero, the incoming differential has zero range, so exactness says
that the kernel of the based degree-zero differential is bottom.  In positive
degree this is the ordinary equality `range d = ker d`; reduced and ordinary
cohomology agree there. -/
def ReducedCohomologyZeroAt (b : V) : ℕ → Prop
  | 0 => LinearMap.ker (basedZeroCoboundary (G := G) M b) = ⊥
  | n + 1 =>
      LinearMap.range (coboundary (G := G) M n) =
        LinearMap.ker (coboundary (G := G) M (n + 1))

/-! ## The ambient cone contraction -/

/-- The global positive-degree cone homotopy, obtained by identifying the
whole cone with the closed star of its apex. -/
def simplicialConeCocyclePrimitive (n : ℕ)
    (c : Cochain (simplicialCone M) (n + 1) G) :
    Cochain (simplicialCone M) n G :=
  extendCarrierClosedStar (simplicialCone M)
    (coneApexSimplex (simplicialCone M) none) n
    (coneHomotopy (simplicialCone M)
      (coneApexSimplex (simplicialCone M) none) none
      (mem_coneApexSimplex (simplicialCone M) none) n
      (restrictClosedStar (simplicialCone M)
        (coneApexSimplex (simplicialCone M) none) (n + 1) c))

/-- The cone primitive vanishes on every simplex containing the apex. -/
theorem simplicialConeCocyclePrimitive_apexFree (n : ℕ)
    (c : Cochain (simplicialCone M) (n + 1) G)
    (σ : Simplex (simplicialCone M) n)
    (hσ : (none : Option V) ∈ σ.1) :
    simplicialConeCocyclePrimitive M n c σ = 0 := by
  let σStar : ClosedStarSimplex (simplicialCone M)
      (coneApexSimplex (simplicialCone M) none) n :=
    ⟨σ, simplex_mem_apexClosedStar (simplicialCone M)
      (simplicialCone_isConeAt M) σ⟩
  calc
    simplicialConeCocyclePrimitive M n c σ =
        restrictClosedStar (simplicialCone M)
          (coneApexSimplex (simplicialCone M) none) n
          (simplicialConeCocyclePrimitive M n c) σStar := rfl
    _ = coneHomotopy (simplicialCone M)
          (coneApexSimplex (simplicialCone M) none) none
          (mem_coneApexSimplex (simplicialCone M) none) n
          (restrictClosedStar (simplicialCone M)
            (coneApexSimplex (simplicialCone M) none) (n + 1) c) σStar := by
      rw [simplicialConeCocyclePrimitive,
        restrictClosedStar_extendCarrierClosedStar]
    _ = 0 := coneHomotopy_apply_of_mem
      (simplicialCone M) (coneApexSimplex (simplicialCone M) none) none
      (mem_coneApexSimplex (simplicialCone M) none) n _ σStar hσ

/-- On a cocycle, the ambient cone homotopy is an actual primitive. -/
theorem coboundary_simplicialConeCocyclePrimitive (n : ℕ)
    (c : Cochain (simplicialCone M) (n + 1) G)
    (hc : coboundary (simplicialCone M) (n + 1) c = 0) :
    coboundary (simplicialCone M) n
        (simplicialConeCocyclePrimitive M n c) = c := by
  apply restrictClosedStar_apex_injective (G := G) (simplicialCone M)
    (simplicialCone_isConeAt M) (n + 1)
  have hnat := LinearMap.congr_fun
    (restrictClosedStar_coboundary (G := G) (simplicialCone M)
      (coneApexSimplex (simplicialCone M) none) n)
    (simplicialConeCocyclePrimitive M n c)
  simp only [LinearMap.comp_apply] at hnat
  rw [hnat, simplicialConeCocyclePrimitive,
    restrictClosedStar_extendCarrierClosedStar]
  have hcontract := closedStar_contraction_positive
    (G := G) (simplicialCone M)
    (coneApexSimplex (simplicialCone M) none) none
    (mem_coneApexSimplex (simplicialCone M) none) n
    (restrictClosedStar (simplicialCone M)
      (coneApexSimplex (simplicialCone M) none) (n + 1) c)
  have hdc :
      closedStarCoboundary (simplicialCone M)
        (coneApexSimplex (simplicialCone M) none) (n + 1)
        (restrictClosedStar (simplicialCone M)
          (coneApexSimplex (simplicialCone M) none) (n + 1) c) = 0 := by
    have hnat' := LinearMap.congr_fun
      (restrictClosedStar_coboundary (G := G) (simplicialCone M)
        (coneApexSimplex (simplicialCone M) none) (n + 1)) c
    simp only [LinearMap.comp_apply] at hnat'
    rw [← hnat', hc, map_zero]
  rw [hdc, map_zero, add_zero] at hcontract
  exact hcontract

/-! ## Restricting an apex-free primitive to the pointed pair -/

/-- In positive degree, an apex-free cochain restricts to the collapse of
its bottom restriction.  This is the small geometric observation that makes
the relative correction below work on the whole pair, including the
distinguished edge. -/
theorem pair_pullback_eq_pointedConePairCochain_of_apexFree_succ
    (b : V) (n : ℕ) (a : Cochain (simplicialCone M) (n + 1) G)
    (ha : ∀ σ, (none : Option V) ∈ σ.1 → a σ = 0) :
    (pointedConePairInclusion M b).pullback (n + 1) a =
      pointedConePairCochain M b (n + 1)
        ((coneBottomInclusion M).pullback (n + 1) a) := by
  ext τ
  by_cases hnone : (none : Option V) ∈ τ.1
  · have hp := (mem_pointedConePair M b τ.1).mp τ.2.1
    have hedge : τ.1 ⊆ (pointedConePairEdge M b).1 := by
      rcases hp.2 with havoid | hedge
      · exact (havoid hnone).elim
      · simpa [pointedConePairEdge, coneBasepointEdgeFacet,
          basepointFacet] using hedge
    let η : facesIn (pointedConePair M b) (n + 1)
        (pointedConePairEdge M b) := ⟨τ, hedge⟩
    rw [pointedConePairCochain_succ_on_edge M b n _ η]
    rw [OrderedSimplicialMap.pullback_apply]
    apply ha
    change none ∈ τ.1.map
      (pointedConePairInclusion M b).toOrderEmbedding.toEmbedding
    simpa [pointedConePairInclusion] using hnone
  · rcases exists_bottom_simplex_of_apex_not_mem M b (n + 1) τ hnone with
      ⟨σ, rfl⟩
    change
      a ((pointedConePairInclusion M b).mapSimplex
          ((pointedConePairBottomInclusion M b).mapSimplex σ)) =
        (pointedConePairBottomInclusion M b).extendCochainByZero (n + 1)
          ((coneBottomInclusion M).pullback (n + 1) a)
          ((pointedConePairBottomInclusion M b).mapSimplex σ)
    rw [OrderedSimplicialMap.extendCochainByZero_apply_of_eq]
    have hfactor := congrArg
      (fun c : Cochain M (n + 1) G => c σ)
      (coneBottom_pullback_eq_pair_pullback
        (G := G) M b (n + 1) a)
    exact hfactor.symm

/-- The arbitrary pointed lift used in Section 4 restricts to the prescribed
collapse cochain on the entire pointed pair. -/
@[simp]
theorem pair_pullback_pointedConeArbitraryCochainLift
    (b : V) (n : ℕ) (c : Cochain M n G) :
    (pointedConePairInclusion M b).pullback n
        (pointedConeArbitraryCochainLift M b n c) =
      pointedConePairCochain M b n c := by
  exact OrderedSimplicialMap.pullback_extendCochainByZero
    (pointedConePairInclusion M b) n (pointedConePairCochain M b n c)

/-- Coboundary on the distinguished oriented edge is bottom value minus
apex value. -/
theorem coboundary_pointedConePair_edge_apply
    (b : V) (u : Cochain (pointedConePair M b) 0 G) :
    coboundary (pointedConePair M b) 0 u
        (pointedConePairEdgeSimplex M b) =
      u ((pointedConePairBottomInclusion M b).mapSimplex
          (basepointSimplex M b)) -
        u (basepointSimplex (pointedConePair M b) none) := by
  rw [coboundary_apply]
  let va : (pointedConePairEdgeSimplex M b).1 :=
    ⟨none, by simp [pointedConePairEdgeSimplex, pointedConePairEdge,
      coneBasepointEdgeFacet, basepointFacet]⟩
  let vb : (pointedConePairEdgeSimplex M b).1 :=
    ⟨some b, by simp [pointedConePairEdgeSimplex, pointedConePairEdge,
      coneBasepointEdgeFacet, basepointFacet]⟩
  let f : (pointedConePairEdgeSimplex M b).1 → G := fun x =>
    incidenceSign (pointedConePair M b)
        (pointedConePairEdgeSimplex M b) x.1 •
      u (eraseVertex (pointedConePair M b)
        (pointedConePairEdgeSimplex M b) x.1 x.2)
  change (∑ x, f x) = _
  rw [Fintype.sum_eq_add_sum_subtype_ne f va]
  have hvab : vb ≠ va := by
    intro h
    exact Option.some_ne_none b (congrArg (fun x => x.1) h)
  have hremaining : (∑ x : {x // x ≠ va}, f x.1) = f vb := by
    rw [Fintype.sum_eq_single ⟨vb, hvab⟩]
    intro x hx
    exfalso
    apply hx
    apply Subtype.ext
    apply Subtype.ext
    have hxmem : x.1.1 ∈ ({none, some b} : Finset (Option V)) := by
      simpa [pointedConePairEdgeSimplex, pointedConePairEdge,
        coneBasepointEdgeFacet, basepointFacet] using x.1.2
    rcases Finset.mem_insert.mp hxmem with hxnone | hxsome
    · exfalso
      apply x.2
      apply Subtype.ext
      exact hxnone
    · exact Finset.mem_singleton.mp hxsome
  rw [hremaining]
  have heraseNone :
      eraseVertex (pointedConePair M b) (pointedConePairEdgeSimplex M b)
          va.1 va.2 =
        (pointedConePairBottomInclusion M b).mapSimplex
          (basepointSimplex M b) := by
    apply Subtype.ext
    change ({none, some b} : Finset (Option V)).erase none = {some b}
    simp
  have heraseSome :
      eraseVertex (pointedConePair M b) (pointedConePairEdgeSimplex M b)
          vb.1 vb.2 =
        basepointSimplex (pointedConePair M b) none := by
    apply Subtype.ext
    change ({none, some b} : Finset (Option V)).erase (some b) = {none}
    ext o
    cases o <;> simp
  have hsignNone :
      incidenceSign (pointedConePair M b)
          (pointedConePairEdgeSimplex M b) va.1 = 1 := by
    have hfilter :
        ({none, some b} : Finset (Option V)).filter
            (fun x => x < none) = ∅ := by
      ext x
      constructor
      · intro hx
        have hxlt := (Finset.mem_filter.mp hx).2
        exact (not_lt_of_ge (show (none : Option V) ≤ x by
          change (⊥ : WithBot V) ≤ x
          exact bot_le) hxlt).elim
      · intro hx
        simpa using hx
    simp [incidenceSign, va, pointedConePairEdgeSimplex,
      pointedConePairEdge, coneBasepointEdgeFacet, basepointFacet, hfilter]
  have hsignSome :
      incidenceSign (pointedConePair M b)
          (pointedConePairEdgeSimplex M b) vb.1 = -1 := by
    have hlt : (none : Option V) < some b := by
      change (⊥ : WithBot V) < (b : WithBot V)
      exact WithBot.bot_lt_coe b
    have hfilter :
        ({none, some b} : Finset (Option V)).filter
            (fun x => x < some b) = {none} := by
      ext x
      constructor
      · intro hx
        rcases Finset.mem_insert.mp (Finset.mem_filter.mp hx).1 with
          hnone | hsome
        · exact Finset.mem_singleton.mpr hnone
        · have hxb : x = some b := Finset.mem_singleton.mp hsome
          subst x
          exact (lt_irrefl _ (Finset.mem_filter.mp hx).2).elim
      · intro hx
        have hnone : x = none := Finset.mem_singleton.mp hx
        subst x
        exact Finset.mem_filter.mpr ⟨Finset.mem_insert_self _ _, hlt⟩
    simp [incidenceSign, vb, pointedConePairEdgeSimplex,
      pointedConePairEdge, coneBasepointEdgeFacet, basepointFacet, hfilter]
  simp only [f, hsignNone, hsignSome, one_smul, neg_smul]
  rw [heraseNone, heraseSome]
  rw [sub_eq_add_neg]

/-! ## Positive-degree reduced exactness implies relative exactness -/

/-- The cochain proof of (4.10) in positive reduced degree. -/
theorem pointedConePairRelativeCohomologyZero_of_reduced_succ
    (b : V) (n : ℕ)
    (hred : ReducedCohomologyZeroAt (G := G) M b (n + 1)) :
    PointedConePairRelativeCohomologyZero (G := G) M b (n + 1) := by
  let F := pointedConePairInclusion M b
  apply le_antisymm
  · rintro y ⟨x, rfl⟩
    rw [LinearMap.mem_ker]
    exact F.relativeCoboundary_relativeCoboundary (G := G) (n + 1) x
  · intro γ hγker
    rw [LinearMap.mem_ker] at hγker
    have hγcycle :
        coboundary (simplicialCone M) (n + 2) γ.1 = 0 := by
      exact congrArg Subtype.val hγker
    let a : Cochain (simplicialCone M) (n + 1) G :=
      simplicialConeCocyclePrimitive M (n + 1) γ.1
    let c : Cochain M (n + 1) G :=
      (coneBottomInclusion M).pullback (n + 1) a
    have hbottomγ :
        (coneBottomInclusion M).pullback (n + 2) γ.1 = 0 := by
      rw [coneBottom_pullback_eq_pair_pullback (G := G) M b]
      change (pointedConePairBottomInclusion M b).pullback (n + 2)
        (F.pullback (n + 2) γ.1) = 0
      rw [show F.pullback (n + 2) γ.1 = 0 by exact γ.2]
      simp
    have hcocycle : coboundary M (n + 1) c = 0 := by
      have hnat := LinearMap.congr_fun
        ((coneBottomInclusion M).pullback_coboundary (G := G) (n + 1)) a
      simp only [LinearMap.comp_apply] at hnat
      rw [← hnat, coboundary_simplicialConeCocyclePrimitive
        M (n + 1) γ.1 hγcycle, hbottomγ]
    have hcker : c ∈ LinearMap.ker (coboundary (G := G) M (n + 1)) :=
      hcocycle
    rw [← hred] at hcker
    rcases hcker with ⟨p, hp⟩
    let z : Cochain (simplicialCone M) n G :=
      pointedConeArbitraryCochainLift M b n p
    let aRel : F.RelativeCochain (G := G) (n + 1) :=
      ⟨a - coboundary (simplicialCone M) n z, by
        rw [LinearMap.mem_ker]
        change F.pullback (n + 1)
          (a - coboundary (simplicialCone M) n z) = 0
        rw [map_sub]
        rw [pair_pullback_eq_pointedConePairCochain_of_apexFree_succ
          (G := G) M b n a]
        · have hnat := LinearMap.congr_fun
            (F.pullback_coboundary (G := G) n) z
          simp only [LinearMap.comp_apply] at hnat
          rw [hnat, pair_pullback_pointedConeArbitraryCochainLift,
            coboundary_pointedConePairCochain, hp, sub_self]
        · intro σ hσ
          exact simplicialConeCocyclePrimitive_apexFree
            M (n + 1) γ.1 σ hσ⟩
    refine ⟨aRel, ?_⟩
    apply Subtype.ext
    change coboundary (simplicialCone M) (n + 1)
      (a - coboundary (simplicialCone M) n z) = γ.1
    rw [map_sub, coboundary_simplicialConeCocyclePrimitive
      M (n + 1) γ.1 hγcycle,
      coboundary_coboundary, sub_zero]

/-! ## The reduced degree-zero endpoint -/

/-- The degree-zero case of (4.10).  The distinguished edge is essential
here: it forces the constant represented by a reduced zero-cocycle to be
zero, so that the relative degree-one cocycle itself vanishes. -/
theorem pointedConePairRelativeCohomologyZero_of_reduced_zero
    (b : V) (hred : ReducedCohomologyZeroAt (G := G) M b 0) :
    PointedConePairRelativeCohomologyZero (G := G) M b 0 := by
  let F := pointedConePairInclusion M b
  apply le_antisymm
  · rintro y ⟨x, rfl⟩
    rw [LinearMap.mem_ker]
    exact F.relativeCoboundary_relativeCoboundary (G := G) 0 x
  · intro γ hγker
    rw [LinearMap.mem_ker] at hγker
    have hγcycle : coboundary (simplicialCone M) 1 γ.1 = 0 :=
      congrArg Subtype.val hγker
    let a : Cochain (simplicialCone M) 0 G :=
      simplicialConeCocyclePrimitive M 0 γ.1
    let c : Cochain M 0 G :=
      (coneBottomInclusion M).pullback 0 a
    have hda : coboundary (simplicialCone M) 0 a = γ.1 :=
      coboundary_simplicialConeCocyclePrimitive M 0 γ.1 hγcycle
    have hbottomγ : (coneBottomInclusion M).pullback 1 γ.1 = 0 := by
      rw [coneBottom_pullback_eq_pair_pullback (G := G) M b]
      change (pointedConePairBottomInclusion M b).pullback 1
        (F.pullback 1 γ.1) = 0
      rw [show F.pullback 1 γ.1 = 0 by exact γ.2]
      simp
    have hcocycle : coboundary M 0 c = 0 := by
      have hnat := LinearMap.congr_fun
        ((coneBottomInclusion M).pullback_coboundary (G := G) 0) a
      simp only [LinearMap.comp_apply] at hnat
      rw [← hnat, hda, hbottomγ]
    have hpairCocycle :
        coboundary (pointedConePair M b) 0 (F.pullback 0 a) = 0 := by
      have hnat := LinearMap.congr_fun
        (F.pullback_coboundary (G := G) 0) a
      simp only [LinearMap.comp_apply] at hnat
      rw [← hnat, hda, show F.pullback 1 γ.1 = 0 by exact γ.2]
    have hedge := congrArg
      (fun z : Cochain (pointedConePair M b) 1 G =>
        z (pointedConePairEdgeSimplex M b)) hpairCocycle
    change coboundary (pointedConePair M b) 0 (F.pullback 0 a)
        (pointedConePairEdgeSimplex M b) = 0 at hedge
    rw [coboundary_pointedConePair_edge_apply] at hedge
    have hbottomValue :
        (F.pullback 0 a)
            ((pointedConePairBottomInclusion M b).mapSimplex
              (basepointSimplex M b)) =
          c (basepointSimplex M b) := by
      have hfactor := congrArg
        (fun z : Cochain M 0 G => z (basepointSimplex M b))
        (coneBottom_pullback_eq_pair_pullback (G := G) M b 0 a)
      exact hfactor.symm
    have hapexValue :
        (F.pullback 0 a)
            (basepointSimplex (pointedConePair M b) none) = 0 := by
      rw [OrderedSimplicialMap.pullback_apply]
      apply simplicialConeCocyclePrimitive_apexFree M 0 γ.1
      change none ∈
        (basepointSimplex (pointedConePair M b) none).1.map
          F.toOrderEmbedding.toEmbedding
      simp [F, pointedConePairInclusion, basepointSimplex]
    rw [hbottomValue, hapexValue, sub_zero] at hedge
    let cBased : BasedZeroCochain (G := G) M b := ⟨c, by
      change c (basepointSimplex M b) = 0
      exact hedge⟩
    have hcBasedKer :
        cBased ∈ LinearMap.ker (basedZeroCoboundary (G := G) M b) := by
      rw [LinearMap.mem_ker]
      exact hcocycle
    rw [hred] at hcBasedKer
    have hcBasedZero : cBased = 0 := by simpa using hcBasedKer
    have hcZero : c = 0 := congrArg Subtype.val hcBasedZero
    have haZero : a = 0 := by
      ext σ
      have hcard : σ.1.card = 1 := by simpa using σ.2.2
      obtain ⟨o, ho⟩ := Finset.card_eq_one.mp hcard
      cases o with
      | none =>
          apply simplicialConeCocyclePrimitive_apexFree M 0 γ.1 σ
          simp [ho]
      | some x =>
          have hσ : σ = (coneBottomInclusion M).mapSimplex
              (basepointSimplex M x) := by
            apply Subtype.ext
            simp [ho, OrderedSimplicialMap.mapSimplex,
              coneBottomInclusion, basepointSimplex]
          rw [hσ]
          have hcApply := congrArg
            (fun z : Cochain M 0 G => z (basepointSimplex M x)) hcZero
          exact hcApply
    have hγZero : γ = 0 := by
      apply Subtype.ext
      rw [← hda, haZero, map_zero]
      rfl
    subst γ
    exact ⟨0, by simp⟩

/-! ## Public shift statements -/

/-- Equation (4.10), uniformly in every reduced degree. -/
theorem pointedConePairRelativeCohomologyZero_of_reduced
    (b : V) (n : ℕ)
    (hred : ReducedCohomologyZeroAt (G := G) M b n) :
    PointedConePairRelativeCohomologyZero (G := G) M b n := by
  cases n with
  | zero =>
      exact pointedConePairRelativeCohomologyZero_of_reduced_zero
        (G := G) M b hred
  | succ n =>
      exact pointedConePairRelativeCohomologyZero_of_reduced_succ
        (G := G) M b n hred

/-- The two consecutive shifts used in (4.16--4.17): vanishing in reduced
degrees `n+1` and `n` supplies the two relative exactness statements needed
for the two successive cone extensions. -/
theorem pointedConePairRelativeCohomologyZero_two_shifts
    (b : V) (n : ℕ)
    (hhigh : ReducedCohomologyZeroAt (G := G) M b (n + 1))
    (hlow : ReducedCohomologyZeroAt (G := G) M b n) :
    PointedConePairRelativeCohomologyZero (G := G) M b (n + 1) ∧
      PointedConePairRelativeCohomologyZero (G := G) M b n :=
  ⟨pointedConePairRelativeCohomologyZero_of_reduced
      (G := G) M b (n + 1) hhigh,
    pointedConePairRelativeCohomologyZero_of_reduced
      (G := G) M b n hlow⟩

/-! ## The unpointed cone pair used in (4.16) -/

/-- Positive reduced degree for the ordinary bottom inclusion
`M ⊆ C_vM`. -/
theorem coneBottomRelativeCohomologyZero_of_reduced_succ
    (b : V) (n : ℕ)
    (hred : ReducedCohomologyZeroAt (G := G) M b (n + 1)) :
    (coneBottomInclusion M).RelativeCohomologyZeroAtSucc
      (G := G) (n + 1) := by
  let F := coneBottomInclusion M
  apply le_antisymm
  · rintro y ⟨x, rfl⟩
    rw [LinearMap.mem_ker]
    exact F.relativeCoboundary_relativeCoboundary (G := G) (n + 1) x
  · intro γ hγker
    rw [LinearMap.mem_ker] at hγker
    have hγcycle : coboundary (simplicialCone M) (n + 2) γ.1 = 0 :=
      congrArg Subtype.val hγker
    let a : Cochain (simplicialCone M) (n + 1) G :=
      simplicialConeCocyclePrimitive M (n + 1) γ.1
    let c : Cochain M (n + 1) G := F.pullback (n + 1) a
    have hcocycle : coboundary M (n + 1) c = 0 := by
      have hnat := LinearMap.congr_fun
        (F.pullback_coboundary (G := G) (n + 1)) a
      simp only [LinearMap.comp_apply] at hnat
      rw [← hnat, coboundary_simplicialConeCocyclePrimitive
        M (n + 1) γ.1 hγcycle, show F.pullback (n + 2) γ.1 = 0 by
          exact γ.2]
    have hcker : c ∈ LinearMap.ker (coboundary (G := G) M (n + 1)) :=
      hcocycle
    rw [← hred] at hcker
    rcases hcker with ⟨p, hp⟩
    let z : Cochain (simplicialCone M) n G :=
      F.extendCochainByZero n p
    let aRel : F.RelativeCochain (G := G) (n + 1) :=
      ⟨a - coboundary (simplicialCone M) n z, by
        rw [LinearMap.mem_ker]
        change F.pullback (n + 1)
          (a - coboundary (simplicialCone M) n z) = 0
        rw [map_sub]
        have hnat := LinearMap.congr_fun
          (F.pullback_coboundary (G := G) n) z
        simp only [LinearMap.comp_apply] at hnat
        rw [hnat, OrderedSimplicialMap.pullback_extendCochainByZero,
          hp, sub_self]⟩
    refine ⟨aRel, ?_⟩
    apply Subtype.ext
    change coboundary (simplicialCone M) (n + 1)
      (a - coboundary (simplicialCone M) n z) = γ.1
    rw [map_sub, coboundary_simplicialConeCocyclePrimitive
      M (n + 1) γ.1 hγcycle, coboundary_coboundary, sub_zero]

/-- Reduced degree zero for the ordinary bottom inclusion.  Here the cone
primitive is normalized by subtracting a global constant. -/
theorem coneBottomRelativeCohomologyZero_of_reduced_zero
    (b : V) (hred : ReducedCohomologyZeroAt (G := G) M b 0) :
    (coneBottomInclusion M).RelativeCohomologyZeroAtSucc
      (G := G) 0 := by
  let F := coneBottomInclusion M
  apply le_antisymm
  · rintro y ⟨x, rfl⟩
    rw [LinearMap.mem_ker]
    exact F.relativeCoboundary_relativeCoboundary (G := G) 0 x
  · intro γ hγker
    rw [LinearMap.mem_ker] at hγker
    have hγcycle : coboundary (simplicialCone M) 1 γ.1 = 0 :=
      congrArg Subtype.val hγker
    let a : Cochain (simplicialCone M) 0 G :=
      simplicialConeCocyclePrimitive M 0 γ.1
    let c : Cochain M 0 G := F.pullback 0 a
    have hda : coboundary (simplicialCone M) 0 a = γ.1 :=
      coboundary_simplicialConeCocyclePrimitive M 0 γ.1 hγcycle
    have hcocycle : coboundary M 0 c = 0 := by
      have hnat := LinearMap.congr_fun
        (F.pullback_coboundary (G := G) 0) a
      simp only [LinearMap.comp_apply] at hnat
      rw [← hnat, hda, show F.pullback 1 γ.1 = 0 by exact γ.2]
    let cNorm : Cochain M 0 G :=
      c - constantCochain M (c (basepointSimplex M b))
    have hcNormBased : cNorm ∈ BasedZeroCochain (G := G) M b := by
      change cNorm (basepointSimplex M b) = 0
      simp [cNorm]
    let cNormBased : BasedZeroCochain (G := G) M b :=
      ⟨cNorm, hcNormBased⟩
    have hcNormCycle : coboundary M 0 cNorm = 0 := by
      simp [cNorm, hcocycle]
    have hcNormKer :
        cNormBased ∈ LinearMap.ker (basedZeroCoboundary (G := G) M b) := by
      rw [LinearMap.mem_ker]
      exact hcNormCycle
    rw [hred] at hcNormKer
    have hcNormZero : cNorm = 0 := by
      have : cNormBased = 0 := by simpa using hcNormKer
      exact congrArg Subtype.val this
    let aRelValue : Cochain (simplicialCone M) 0 G :=
      a - constantCochain (simplicialCone M)
        (c (basepointSimplex M b))
    let aRel : F.RelativeCochain (G := G) 0 :=
      ⟨aRelValue, by
        rw [LinearMap.mem_ker]
        change F.pullback 0
          (a - constantCochain (simplicialCone M)
            (c (basepointSimplex M b))) = 0
        rw [map_sub]
        have hconstant : F.pullback 0
            (constantCochain (simplicialCone M)
              (c (basepointSimplex M b))) =
            constantCochain M (c (basepointSimplex M b)) := by
          ext σ
          rfl
        rw [hconstant]
        exact sub_eq_zero.mpr (sub_eq_zero.mp hcNormZero)⟩
    refine ⟨aRel, ?_⟩
    apply Subtype.ext
    change coboundary (simplicialCone M) 0
      (a - constantCochain (simplicialCone M)
        (c (basepointSimplex M b))) = γ.1
    rw [coboundary_sub_constantCochain, hda]

/-- The ordinary cone-pair exactness used for the first extension in
(4.16), in all reduced degrees. -/
theorem coneBottomRelativeCohomologyZero_of_reduced
    (b : V) (n : ℕ)
    (hred : ReducedCohomologyZeroAt (G := G) M b n) :
    (coneBottomInclusion M).RelativeCohomologyZeroAtSucc (G := G) n := by
  cases n with
  | zero =>
      exact coneBottomRelativeCohomologyZero_of_reduced_zero
        (G := G) M b hred
  | succ n =>
      exact coneBottomRelativeCohomologyZero_of_reduced_succ
        (G := G) M b n hred

/-- The actual fibrewise cochain lift for `M ⊆ C_vM` required by the
first gluing step in (4.16). -/
def coneBottomFiberwiseCochainLiftOfReducedCohomology
    (b : V) (n : ℕ)
    (hred : ReducedCohomologyZeroAt (G := G) M b n) :=
  (coneBottomInclusion M).fiberwiseCochainLiftOfRelativeCohomology n
    (coneBottomRelativeCohomologyZero_of_reduced
      (G := G) M b n hred)

/-! ## The literal double-cone boundary in (4.17) -/

/-- Inside `C_w C_vM`, the union `C_vM ∪_M C_wM` consists exactly of
the simplices which do not contain both cone apices. -/
def doubleConeBoundary :
    AbstractSimplicialComplex (Option (Option V)) where
  faces := {s | s ∈ simplicialCone (simplicialCone M) ∧
    ((none : Option (Option V)) ∉ s ∨
      (some none : Option (Option V)) ∉ s)}
  isRelLowerSet_faces := by
    intro s hs
    refine ⟨(simplicialCone (simplicialCone M)).isRelLowerSet_faces hs.1 |>.1,
      ?_⟩
    intro t hts ht
    refine ⟨(simplicialCone (simplicialCone M)).isRelLowerSet_faces
      hs.1 |>.2 hts ht, ?_⟩
    rcases hs.2 with hsOuter | hsInner
    · exact Or.inl fun h => hsOuter (hts h)
    · exact Or.inr fun h => hsInner (hts h)
  singleton_mem o := by
    refine ⟨(simplicialCone (simplicialCone M)).singleton_mem o, ?_⟩
    cases o with
    | none => exact Or.inr (by simp)
    | some o => exact Or.inl (by simp)

@[simp]
theorem mem_doubleConeBoundary (s : Finset (Option (Option V))) :
    s ∈ doubleConeBoundary M ↔
      s ∈ simplicialCone (simplicialCone M) ∧
        ((none : Option (Option V)) ∉ s ∨
          (some none : Option (Option V)) ∉ s) :=
  Iff.rfl

/-- The literal inclusion
`C_vM ∪_M C_wM ⊆ C_wC_vM`. -/
def doubleConeBoundaryInclusion :
    OrderedSimplicialMap (doubleConeBoundary M)
      (simplicialCone (simplicialCone M)) where
  toOrderEmbedding := OrderEmbedding.id _
  map_mem := by
    intro s hs
    have himage : s.map
        (OrderEmbedding.id (Option (Option V))).toEmbedding = s := by
      ext o
      simp
    rw [himage]
    exact hs.1

end GeneralSphereT.SimplicialCochain
