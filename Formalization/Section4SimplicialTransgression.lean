import Formalization.Section4SimplicialConeExtension
import Formalization.Section4Transgression

set_option linter.style.header false

/-!
# Section 4: the concrete relative extension-class map

This file gives the algebraic specialization of Proposition 4.5.  A chosen
fibrewise cochain lift induces the extension of primitive cycles from `X` to
its literal cone and hence the actual relative section in (4.15).

Cone vanishing proves surjectivity.  Exactness followed by `T'(C_vX)=0`
proves that the kernel is contained in the primitive boundaries.  Thus, for
the canonical algebraic relative quotient, the only remaining input is the
paragraph asserting that a primitive relation boundary contracts relatively;
this is precisely the nonlinear contraction of (4.21).
-/

noncomputable section

namespace GeneralSphereT.SimplicialCochain

open GeneralSphereT.PathAlgebra
open GeneralSphereT.PathAlgebra.FacetRestrictionData
open GeneralSphereT.PathAlgebra.FacetRestrictionHom
open GeneralSphereT.Section4

variable {V G : Type*} [LinearOrder V] [Fintype V] [AddCommGroup G]
variable (X : AbstractSimplicialComplex V) (n : ℕ)

local instance section4TransgressionOptionLinearOrder : LinearOrder (Option V) :=
  @WithBot.linearOrder V inferInstance

/-- Strict `F`-sections on `C_vX` which vanish on the whole bottom `X`.
This is the algebraic presentation of maps `(C_vX,X) → (F,0)`. -/
abbrev ConeRelativeSections :=
  LinearMap.ker (coneBottomStrictFSectionsRestriction (G := G) X n)

/-- Primitive cone relations which vanish already on the bottom. -/
abbrev ConeRelativeRelations :=
  LinearMap.ker (coneBottomRprimRestriction (G := G) X n)

/-- Restriction of a bottom-zero primitive relation is a bottom-zero strict
section. -/
def coneRelativeRestriction :
    ConeRelativeRelations (G := G) X n →ₗ[ℤ]
      ConeRelativeSections (G := G) X n :=
  LinearMap.codRestrict (ConeRelativeSections (G := G) X n)
    ((restrictionClass
      (facetRestrictionData (G := G) (simplicialCone X) n)).comp
        (ConeRelativeRelations (G := G) X n).subtype) fun r => by
          rw [LinearMap.mem_ker]
          have hnat := LinearMap.congr_fun
            (mapStrictFSections_restrictionClass
              (coneBottomFacetHom (G := G) X n)) r.1
          calc
            coneBottomStrictFSectionsRestriction (G := G) X n
                (restrictionClass
                  (facetRestrictionData
                    (G := G) (simplicialCone X) n) r.1) =
                restrictionClass (facetRestrictionData (G := G) X n)
                  (coneBottomRprimRestriction (G := G) X n r.1) := by
              simpa [coneBottomStrictFSectionsRestriction,
                coneBottomRprimRestriction] using hnat
            _ = 0 := by rw [r.2, map_zero]

/-- The algebraic relative-null subgroup: restrictions of primitive
relations which vanish on the bottom. -/
abbrev ConeRelativeNullMaps : Submodule ℤ
    (ConeRelativeSections (G := G) X n) :=
  LinearMap.range (coneRelativeRestriction (G := G) X n)

/-- Every strict section on the literal cone is represented by a primitive
relation.  This is the unpointed form of cone vanishing used in (4.18). -/
theorem coneRestrictionClass_surjective :
    Function.Surjective
      (restrictionClass
        (facetRestrictionData (G := G) (simplicialCone X) n)) := by
  let LC := facetRestrictionData (G := G) (simplicialCone X) n
  let facetsC := fun σ : NonemptySimplex (simplicialCone X) =>
    facesIn (simplicialCone X) n σ
  have hexact : Function.Exact (restrictionClass LC)
      (simplicialObstruction (G := G) (simplicialCone X) n) := by
    exact exact_restrictionClass_obstruction facetsC LC
      (simplicialMapLocallyZero_eq_physicalNonfaceCubeSpan
        (G := G) (simplicialCone X) n)
  intro f
  apply (hexact f).mp
  exact @Subsingleton.elim _
    (literalSimplicialConeTau_subsingleton (G := G) X n)
    (simplicialObstruction (G := G) (simplicialCone X) n f) 0

/-- A cone relation whose bottom restriction is zero determines a strict
relative section. -/
def relativeSectionOfBottomZeroRelation
    (r : Rprim
      (d := coboundaryToRange (G := G) (simplicialCone X) n))
    (hr : coneBottomRprimRestriction (G := G) X n r = 0) :
    ConeRelativeSections (G := G) X n :=
  ⟨restrictionClass
      (facetRestrictionData (G := G) (simplicialCone X) n) r,
    by
      rw [LinearMap.mem_ker]
      have hnat := LinearMap.congr_fun
        (mapStrictFSections_restrictionClass
          (coneBottomFacetHom (G := G) X n)) r
      calc
        coneBottomStrictFSectionsRestriction (G := G) X n
            (restrictionClass
              (facetRestrictionData (G := G) (simplicialCone X) n) r) =
            restrictionClass (facetRestrictionData (G := G) X n)
              (coneBottomRprimRestriction (G := G) X n r) := by
          simpa [coneBottomStrictFSectionsRestriction,
            coneBottomRprimRestriction] using hnat
        _ = 0 := by rw [hr, map_zero]⟩

@[simp]
theorem coneRelativeRestriction_mk
    (r : Rprim
      (d := coboundaryToRange (G := G) (simplicialCone X) n))
    (hr : coneBottomRprimRestriction (G := G) X n r = 0) :
    coneRelativeRestriction (G := G) X n ⟨r, hr⟩ =
      relativeSectionOfBottomZeroRelation (G := G) X n r hr := by
  rfl

/-- A generic relative-null quotient may be larger than the canonical
algebraic one.  To use such a quotient, one supplies the relative-uniqueness
statement that a relation already zero on the bottom is null there. -/
structure ConeRelativeUniquenessData
    (RelativeNullMaps : Submodule ℤ
      (ConeRelativeSections (G := G) X n)) where
  relation_null :
    ∀ (r : Rprim
      (d := coboundaryToRange (G := G) (simplicialCone X) n))
      (hr : coneBottomRprimRestriction (G := G) X n r = 0),
      relativeSectionOfBottomZeroRelation (G := G) X n r hr ∈
        RelativeNullMaps

/-- A chosen additive extension of primitive cycles to primitive relations on
the cone.  Its bottom restriction is the original cycle. -/
structure ConeCycleExtensionData where
  extendCycle :
    Zprim (facetRestrictionData (G := G) X n) →ₗ[ℤ]
      Rprim (d := coboundaryToRange (G := G) (simplicialCone X) n)
  restrict_extend :
    (coneBottomRprimRestriction (G := G) X n).comp extendCycle =
      zprimToRprim (facetRestrictionData (G := G) X n)

namespace ConeCycleExtensionData

/-- Lemma 4.2 supplies the extension used in (4.15): apply its additive
relation section to a primitive cycle. -/
def ofFiberwiseCochainLift
    (Q : FiberwiseCochainLift
      (coboundaryToRange (G := G) X n)
      (coboundaryToRange (G := G) (simplicialCone X) n)
      (coneBottomFacetHom (G := G) X n).primitiveMap) :
    ConeCycleExtensionData (G := G) X n := by
  let cycleKernel :
      Zprim (facetRestrictionData (G := G) X n) →ₗ[ℤ]
        LinearMap.ker
          (mapRedDist (coboundaryToRange (G := G) X n)) :=
    LinearMap.codRestrict
      (LinearMap.ker
        (mapRedDist (coboundaryToRange (G := G) X n)))
      (Zprim (facetRestrictionData (G := G) X n)).subtype
      fun z => z.2.1
  refine
    { extendCycle := Q.relationSection.comp cycleKernel
      restrict_extend := ?_ }
  apply LinearMap.ext
  intro z
  apply Subtype.ext
  change mapRedDist
      (coneBottomFacetHom (G := G) X n).primitiveMap
      (Q.relationSection
        (cycleKernel z)).1 = z.1
  calc
    _ = (cycleKernel z).1 := Q.mapRedDist_relationSection (cycleKernel z)
    _ = z.1 := rfl

variable (E : ConeCycleExtensionData (G := G) X n)

/-- The strict relative section represented by an extended primitive cycle.
Bottom vanishing follows from naturality and the defining local-zero property
of `Zprim`. -/
def extensionSection :
    Zprim (facetRestrictionData (G := G) X n) →ₗ[ℤ]
      ConeRelativeSections (G := G) X n :=
  LinearMap.codRestrict (ConeRelativeSections (G := G) X n)
    ((restrictionClass
      (facetRestrictionData (G := G) (simplicialCone X) n)).comp
        E.extendCycle) fun s => by
          rw [LinearMap.mem_ker]
          have hnat := LinearMap.congr_fun
            (mapStrictFSections_restrictionClass
              (coneBottomFacetHom (G := G) X n))
            (E.extendCycle s)
          have hext := LinearMap.congr_fun E.restrict_extend s
          calc
            coneBottomStrictFSectionsRestriction (G := G) X n
                (restrictionClass
                  (facetRestrictionData
                    (G := G) (simplicialCone X) n)
                  (E.extendCycle s)) =
                restrictionClass (facetRestrictionData (G := G) X n)
                  (coneBottomRprimRestriction (G := G) X n
                    (E.extendCycle s)) := by
              simpa [coneBottomStrictFSectionsRestriction,
                coneBottomRprimRestriction] using hnat
            _ = restrictionClass (facetRestrictionData (G := G) X n)
                  (zprimToRprim (facetRestrictionData (G := G) X n) s) := by
              simpa using congrArg
                (fun f : Rprim
                    (d := coboundaryToRange (G := G) X n) =>
                  restrictionClass (facetRestrictionData (G := G) X n) f)
                hext
            _ = 0 := by
              exact LinearMap.congr_fun
                (exact_zprimToRprim_restrictionClass
                  (facetRestrictionData (G := G) X n)).linearMap_comp_eq_zero s

@[simp]
theorem extensionSection_coe
    (s : Zprim (facetRestrictionData (G := G) X n)) :
    (E.extensionSection (X := X) (n := n) s :
        StrictFSections
          (facetRestrictionData (G := G) (simplicialCone X) n)) =
      restrictionClass
        (facetRestrictionData (G := G) (simplicialCone X) n)
        (E.extendCycle s) :=
  rfl

/-- The relative extension-class map of (4.15), with relative homotopy
classes presented as a quotient by a chosen null submodule. -/
def extensionClass
    (RelativeNullMaps : Submodule ℤ
      (ConeRelativeSections (G := G) X n)) :
    Zprim (facetRestrictionData (G := G) X n) →ₗ[ℤ]
      ((ConeRelativeSections (G := G) X n) ⧸ RelativeNullMaps) :=
  relativeClassMap RelativeNullMaps E.extensionSection

@[simp]
theorem extensionClass_apply
    (RelativeNullMaps : Submodule ℤ
      (ConeRelativeSections (G := G) X n))
    (s : Zprim (facetRestrictionData (G := G) X n)) :
    E.extensionClass (X := X) (n := n) RelativeNullMaps s =
      RelativeNullMaps.mkQ (E.extensionSection (X := X) (n := n) s) :=
  rfl

/-- Cone vanishing makes the extension-class map surjective.  Starting with
a relative section, choose a cone relation representing it.  Its bottom is a
cycle; subtract the chosen extension of that cycle.  The remainder is zero
on the bottom and hence relatively null by `ConeRelativeUniquenessData`. -/
theorem extensionClass_surjective
    (RelativeNullMaps : Submodule ℤ
      (ConeRelativeSections (G := G) X n))
    (U : ConeRelativeUniquenessData (G := G) X n RelativeNullMaps) :
    Function.Surjective
      (E.extensionClass (X := X) (n := n) RelativeNullMaps) := by
  intro y
  obtain ⟨f, rfl⟩ := RelativeNullMaps.mkQ_surjective y
  obtain ⟨r, hr⟩ := coneRestrictionClass_surjective
    (G := G) X n f.1
  have hbottomCycle :
      restrictionClass (facetRestrictionData (G := G) X n)
        (coneBottomRprimRestriction (G := G) X n r) = 0 := by
    have hnat := LinearMap.congr_fun
      (mapStrictFSections_restrictionClass
        (coneBottomFacetHom (G := G) X n)) r
    calc
      restrictionClass (facetRestrictionData (G := G) X n)
          (coneBottomRprimRestriction (G := G) X n r) =
          coneBottomStrictFSectionsRestriction (G := G) X n
            (restrictionClass
              (facetRestrictionData (G := G) (simplicialCone X) n) r) := by
        simpa [coneBottomStrictFSectionsRestriction,
          coneBottomRprimRestriction] using hnat.symm
      _ = coneBottomStrictFSectionsRestriction (G := G) X n f.1 := by
        rw [hr]
      _ = 0 := f.2
  obtain ⟨s, hs⟩ :=
    (exact_zprimToRprim_restrictionClass
      (facetRestrictionData (G := G) X n)
      (coneBottomRprimRestriction (G := G) X n r)).mp hbottomCycle
  let k : Rprim
      (d := coboundaryToRange (G := G) (simplicialCone X) n) :=
    r - E.extendCycle s
  have hk : coneBottomRprimRestriction (G := G) X n k = 0 := by
    dsimp [k]
    rw [map_sub]
    have hext := LinearMap.congr_fun E.restrict_extend s
    rw [show coneBottomRprimRestriction (G := G) X n
          (E.extendCycle s) =
        zprimToRprim (facetRestrictionData (G := G) X n) s by
      simpa using hext]
    rw [hs]
    exact sub_self _
  have hdifference :
      f - E.extensionSection (X := X) (n := n) s =
        relativeSectionOfBottomZeroRelation (G := G) X n k hk := by
    apply Subtype.ext
    change f.1 - restrictionClass
        (facetRestrictionData (G := G) (simplicialCone X) n)
          (E.extendCycle s) =
      restrictionClass
        (facetRestrictionData (G := G) (simplicialCone X) n) k
    rw [← hr]
    simp [k]
  refine ⟨s, ?_⟩
  rw [extensionClass_apply]
  apply (Submodule.Quotient.eq RelativeNullMaps).2
  have hnull := U.relation_null k hk
  rw [← hdifference] at hnull
  simpa only [neg_sub] using RelativeNullMaps.neg_mem hnull

/-- The canonical relative extension-class map.  Here the quotient is by
the actual image of bottom-zero primitive relations, so relative uniqueness
is definitional rather than an additional hypothesis. -/
abbrev canonicalExtensionClass :
    Zprim (facetRestrictionData (G := G) X n) →ₗ[ℤ]
      (ConeRelativeSections (G := G) X n ⧸
        ConeRelativeNullMaps (G := G) X n) :=
  E.extensionClass (X := X) (n := n)
    (ConeRelativeNullMaps (G := G) X n)

/-- Surjectivity in Proposition 4.5 follows formally from cone vanishing;
there is no longer a separate `representative_exists` input. -/
theorem canonicalExtensionClass_surjective :
    Function.Surjective (E.canonicalExtensionClass (X := X) (n := n)) := by
  apply E.extensionClass_surjective (X := X) (n := n)
  refine ⟨?_⟩
  intro r hr
  refine ⟨⟨r, hr⟩, ?_⟩
  exact coneRelativeRestriction_mk (G := G) X n r hr

/-- A relatively zero extension class is a primitive boundary on the
bottom.  The proof is the quotient calculation behind the injectivity half
of Proposition 4.5: compare the chosen extension with a bottom-zero cone
relation, obtain a cone cycle from exactness, use `T'(C_vX)=0`, and restrict
that cone boundary back to `X`. -/
theorem canonicalExtensionClass_kernel_le_boundary :
    LinearMap.ker (E.canonicalExtensionClass (X := X) (n := n)) ≤
      BprimInZprim (facetRestrictionData (G := G) X n) := by
  intro z hz
  rw [LinearMap.mem_ker] at hz
  have hzNull : E.extensionSection (X := X) (n := n) z ∈
      ConeRelativeNullMaps (G := G) X n := by
    apply (Submodule.Quotient.mk_eq_zero
      (ConeRelativeNullMaps (G := G) X n)).mp
    exact hz
  rcases hzNull with ⟨k, hk⟩
  have hrestriction :
      restrictionClass
          (facetRestrictionData (G := G) (simplicialCone X) n) k.1 =
        restrictionClass
          (facetRestrictionData (G := G) (simplicialCone X) n)
          (E.extendCycle z) := by
    have hval := congrArg Subtype.val hk
    simpa [coneRelativeRestriction, extensionSection] using hval
  have hcycle :
      restrictionClass
          (facetRestrictionData (G := G) (simplicialCone X) n)
          (E.extendCycle z - k.1) = 0 := by
    rw [map_sub, hrestriction, sub_self]
  obtain ⟨c, hc⟩ :=
    (exact_zprimToRprim_restrictionClass
      (facetRestrictionData (G := G) (simplicialCone X) n)
      (E.extendCycle z - k.1)).mp hcycle
  let F := coneBottomFacetHom (G := G) X n
  have hbottom : mapZprim F c = z := by
    apply zprimToRprim_injective
      (L := facetRestrictionData (G := G) X n)
    have hext := LinearMap.congr_fun E.restrict_extend z
    have hmapCycle :
        coneBottomRprimRestriction (G := G) X n
            (zprimToRprim
              (facetRestrictionData (G := G) (simplicialCone X) n) c) =
          zprimToRprim (facetRestrictionData (G := G) X n)
            (mapZprim F c) := by
      apply Subtype.ext
      rfl
    calc
      zprimToRprim (facetRestrictionData (G := G) X n)
          (mapZprim F c) =
          coneBottomRprimRestriction (G := G) X n
            (zprimToRprim
              (facetRestrictionData (G := G) (simplicialCone X) n) c) :=
        hmapCycle.symm
      _ = coneBottomRprimRestriction (G := G) X n
            (E.extendCycle z - k.1) := by rw [hc]
      _ = coneBottomRprimRestriction (G := G) X n
              (E.extendCycle z) -
            coneBottomRprimRestriction (G := G) X n k.1 := by
        rw [map_sub]
      _ = zprimToRprim
              (facetRestrictionData (G := G) X n) z - 0 := by
            rw [show coneBottomRprimRestriction (G := G) X n
                  (E.extendCycle z) =
                zprimToRprim (facetRestrictionData (G := G) X n) z by
              simpa using hext]
            rw [k.2]
      _ = zprimToRprim (facetRestrictionData (G := G) X n) z := by simp
  have hcBoundary : c ∈ BprimInZprim
      (facetRestrictionData (G := G) (simplicialCone X) n) := by
    apply (Submodule.Quotient.mk_eq_zero
      (BprimInZprim
        (facetRestrictionData (G := G) (simplicialCone X) n))).mp
    exact simplicialConeTPrime_eq_zero (G := G) X n
      ((BprimInZprim
        (facetRestrictionData (G := G) (simplicialCone X) n)).mkQ c)
  have hrestrictBoundary :=
    BprimInZprim_le_comap_mapZprim F hcBoundary
  simpa [hbottom] using hrestrictBoundary

/-- The only remaining kernel input: primitive boundaries extend to
relative-null cone sections.  The reverse inclusion and surjectivity are
theorems above, not fields of this structure. -/
structure ConeBoundaryNullData where
  boundaries_null :
    BprimInZprim (facetRestrictionData (G := G) X n) ≤
      LinearMap.ker
        (E.canonicalExtensionClass (X := X) (n := n))

namespace ConeBoundaryNullData

/-- All three transgression checks, with two of them now discharged by the
literal cone calculation. -/
theorem toTransgressionProofData
    (N : ConeBoundaryNullData (G := G) X n E) :
    GeneralSphereT.Section4.TransgressionProofData
      (BprimInZprim (facetRestrictionData (G := G) X n))
      (E.canonicalExtensionClass (X := X) (n := n)) where
  boundaries_null := ConeBoundaryNullData.boundaries_null N
  relative_zero_is_boundary :=
    E.canonicalExtensionClass_kernel_le_boundary (X := X) (n := n)
  representative_exists :=
    E.canonicalExtensionClass_surjective (X := X) (n := n)

/-- Proposition 4.5 in its concrete simplicial form. -/
def transgressionEquiv
    (N : ConeBoundaryNullData (G := G) X n E) :
    TPrime (facetRestrictionData (G := G) X n) ≃ₗ[ℤ]
      (ConeRelativeSections (G := G) X n ⧸
        ConeRelativeNullMaps (G := G) X n) :=
  ((toTransgressionProofData (X := X) (n := n) (E := E) N)).linearEquiv

/-- The representative formula (4.18). -/
@[simp]
theorem transgressionEquiv_mkQ
    (N : ConeBoundaryNullData (G := G) X n E)
    (z : Zprim (facetRestrictionData (G := G) X n)) :
    transgressionEquiv (X := X) (n := n) (E := E) N
        ((BprimInZprim (facetRestrictionData (G := G) X n)).mkQ z) =
      E.canonicalExtensionClass (X := X) (n := n) z :=
  (toTransgressionProofData (X := X) (n := n)
    (E := E) N).linearEquiv_mkQ z

end ConeBoundaryNullData

end ConeCycleExtensionData

namespace PointedConeFiberwiseLiftData

variable {b : V}

/-- The very same fibrewise lift used for the pointed cone criterion supplies
the cycle extension entering the transgression construction. -/
def toConeCycleExtensionData
    (Q : PointedConeFiberwiseLiftData (G := G) X b n) :
    ConeCycleExtensionData (G := G) X n :=
  ConeCycleExtensionData.ofFiberwiseCochainLift (X := X) (n := n)
    Q.fiberwise

end PointedConeFiberwiseLiftData

end GeneralSphereT.SimplicialCochain
