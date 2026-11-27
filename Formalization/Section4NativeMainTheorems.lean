import Formalization.Section4LiteralDoubleConeDifferenceReverse
import Formalization.Section4NativeTheta
import Formalization.Section4NativeTransgressionEquiv
import Formalization.Section4ReducedFreeHomologyShift
import Formalization.Section4SuspensionCohomologyShift
import Formalization.Section4SuspensionDegreeZero

set_option linter.style.header false

/-!
# Section 4: native main theorems

This is the public endpoint of the Lean formalization of Section 4.  Its
three mapping-class groups are Mathlib's genuine simplicial homotopy-class
quotients:

* `SimplicialTau G M q` is the degree-zero obstruction group `τ(M)`;
* `SimplicialTPrime G M q` is the primitive quotient `T'(M)`;
* `NativeConeQuotientHomotopyClasses M A` presents
  `[C_v M / M, A]_*`, hence, by the standard loop--suspension adjunction,
  `[M, Ω A]_*`.

Thus (4.24) is recorded using the cone-quotient presentation itself.  No
abstract loop-comparison input is introduced.  The suspension comparison
below is literally the composite of native transgression, inverse literal
two-cone difference, and inverse native `θ` on the ordered suspension.
-/

noncomputable section

open CategoryTheory

namespace GeneralSphereT.SimplicialCochain

open GeneralSphereT.PathAlgebra
open GeneralSphereT.PathAlgebra.FacetRestrictionData
open GeneralSphereT.Section4
open GeneralSphereT.Section4.NativeRelativeHomotopyGroup
open GeneralSphereT.StandardModels

universe u

variable {V G : Type u} [LinearOrder V] [Fintype V] [AddCommGroup G]

local instance (priority := 10000) nativeMainOptionLE : LE (Option V) :=
  @WithBot.instLE V inferInstance

local instance (priority := 10000) nativeMainOptionLT : LT (Option V) :=
  @WithBot.instLT V inferInstance

local instance (priority := 10000) nativeMainOptionLinearOrder :
    LinearOrder (Option V) :=
  @WithBot.linearOrder V inferInstance

local instance (priority := 10001) nativeMainOptionOptionLE :
    LE (Option (Option V)) :=
  @WithBot.instLE (Option V) inferInstance

local instance (priority := 10001) nativeMainOptionOptionLT :
    LT (Option (Option V)) :=
  @WithBot.instLT (Option V) inferInstance

local instance (priority := 10001) nativeMainOptionOptionLinearOrder :
    LinearOrder (Option (Option V)) :=
  @WithBot.linearOrder (Option V) inferInstance

/-- The simplicial-cochain specialization of the paper's group `τ(M)`. -/
abbrev SimplicialTau
    (G : Type u) [AddCommGroup G]
    {W : Type u} [LinearOrder W] [Fintype W]
    (M : AbstractSimplicialComplex W) (q : ℕ) :=
  Tau (fun sigma : NonemptySimplex M ↦ facesIn M q sigma)
    (facetRestrictionData (G := G) M q)

/-- The simplicial-cochain specialization of the primitive quotient
`T'(M)`. -/
abbrev SimplicialTPrime
    (G : Type u) [AddCommGroup G]
    {W : Type u} [LinearOrder W] [Fintype W]
    (M : AbstractSimplicialComplex W) (q : ℕ) :=
  TPrime (facetRestrictionData (G := G) M q)

/-- Native relative homotopy classes on the literal cone pair
`(C_v M, M)`.  This is the cone-quotient presentation of
`[C_v M / M, A]_*`, and therefore the standard presentation of
`[M, Ω A]_*` used in (4.24). -/
abbrev NativeConeQuotientHomotopyClasses
    {W : Type u} [LinearOrder W]
    (M : AbstractSimplicialComplex W)
    (A : SimplicialObject AddCommGrpCat.{u}) :=
  NativeHomotopyClass (literalConeBottomSubcomplex M) A

/-! ## The loop--suspension presentation -/

/-- Formula (4.24), with `[M, ΩF]_*` represented by the standard cone
quotient `[C_vM/M,F]_*`.  The two displayed hypotheses are precisely the
two reduced-cohomology vanishings used by the relative-uniqueness proof;
all extension choices are made internally. -/
def nativeLoopSuspensionEquivOfReduced
    (M : AbstractSimplicialComplex V) (b : V) (n : ℕ)
    (hhigh : ReducedCohomologyZeroAt (G := G) M b (n + 1))
    (hlow : ReducedCohomologyZeroAt (G := G) M b n) :
    SimplicialTPrime G M (n + 1) ≃ₗ[ℤ]
      NativeConeQuotientHomotopyClasses M
        (F (AddCommGrpCat.of G) (n + 2)) :=
  canonicalNativeTransgressionLinearEquivOfReduced
    (G := G) M b n hhigh hlow

/-- Representative formula (4.18), now also the representative formula
for the cone-quotient presentation (4.24). -/
@[simp]
theorem nativeLoopSuspensionEquivOfReduced_mkQ
    (M : AbstractSimplicialComplex V) (b : V) (n : ℕ)
    (hhigh : ReducedCohomologyZeroAt (G := G) M b (n + 1))
    (hlow : ReducedCohomologyZeroAt (G := G) M b n)
    (z : Zprim (facetRestrictionData (G := G) M (n + 1))) :
    nativeLoopSuspensionEquivOfReduced M b n hhigh hlow
        ((BprimInZprim
          (facetRestrictionData (G := G) M (n + 1))).mkQ z) =
      (canonicalConeCycleExtensionDataOfReduced
        (G := G) M b (n + 1) hhigh).nativeExtensionClass
          (M := M) (q := n + 1) z :=
  canonicalNativeTransgressionLinearEquivOfReduced_mkQ
    (G := G) M b n hhigh hlow z

/-- The public loop--suspension equivalence has exactly the canonical
native transgression as its underlying linear map. -/
theorem nativeLoopSuspensionEquivOfReduced_toLinearMap
    (M : AbstractSimplicialComplex V) (b : V) (n : ℕ)
    (hhigh : ReducedCohomologyZeroAt (G := G) M b (n + 1))
    (hlow : ReducedCohomologyZeroAt (G := G) M b n) :
    (nativeLoopSuspensionEquivOfReduced
      (G := G) M b n hhigh hlow).toLinearMap =
        canonicalNativeTransgressionOfReduced M b n hhigh hlow :=
  canonicalNativeTransgressionLinearEquivOfReduced_toLinearMap
    (G := G) M b n hhigh hlow

/-! ## The low endpoint of the loop--suspension presentation -/

/-- Formula (4.24) in the paper's endpoint `q = 1`.  Only
`H~⁰(M;G)=0` is assumed; the apparent `H~⁻¹` condition is automatic for
the nonempty complex supplied by `b`. -/
def nativeLoopSuspensionEquivDegreeZero
    (M : AbstractSimplicialComplex V) (b : V)
    (hred : ReducedCohomologyZeroAt (G := G) M b 0) :
    SimplicialTPrime G M 0 ≃ₗ[ℤ]
      NativeConeQuotientHomotopyClasses M
        (F (AddCommGrpCat.of G) 1) :=
  canonicalNativeTransgressionLinearEquivDegreeZero
    (G := G) M b hred

/-- Representative formula for the `q = 1` loop--suspension endpoint. -/
@[simp]
theorem nativeLoopSuspensionEquivDegreeZero_mkQ
    (M : AbstractSimplicialComplex V) (b : V)
    (hred : ReducedCohomologyZeroAt (G := G) M b 0)
    (z : Zprim (facetRestrictionData (G := G) M 0)) :
    nativeLoopSuspensionEquivDegreeZero M b hred
        ((BprimInZprim
          (facetRestrictionData (G := G) M 0)).mkQ z) =
      (canonicalConeCycleExtensionDataOfReduced
        (G := G) M b 0 hred).nativeExtensionClass
          (M := M) (q := 0) z :=
  canonicalNativeTransgressionLinearEquivDegreeZero_mkQ
    (G := G) M b hred z

/-- The endpoint equivalence has exactly the canonical degree-zero
transgression as its underlying map. -/
theorem nativeLoopSuspensionEquivDegreeZero_toLinearMap
    (M : AbstractSimplicialComplex V) (b : V)
    (hred : ReducedCohomologyZeroAt (G := G) M b 0) :
    (nativeLoopSuspensionEquivDegreeZero
      (G := G) M b hred).toLinearMap =
        canonicalNativeTransgressionDegreeZero (G := G) M b hred :=
  canonicalNativeTransgressionLinearEquivDegreeZero_toLinearMap
    (G := G) M b hred

/-! ## The suspension comparison in positive cochain degree -/

/-- Formula (4.26) for paper degree `q = n + 2`, hence `q ≥ 2`.

The map is, definitionally, the composite
`θ_{ΣM}^{-1} ∘ δ^{-1} ∘ Tr`: first transgress a primitive class to the
literal cone quotient, then invert the inner-minus-other two-cone
difference, and finally invert the native degree-zero comparison on the
ordered suspension.  Its only hypotheses are the two reduced-cohomology
vanishings appearing in the paper. -/
def nativeSuspensionEquivOfReduced
    (M : AbstractSimplicialComplex V) (b : V) (n : ℕ)
    (hhigh : ReducedCohomologyZeroAt (G := G) M b (n + 1))
    (hlow : ReducedCohomologyZeroAt (G := G) M b n) :
    SimplicialTPrime G M (n + 1) ≃ₗ[ℤ]
      SimplicialTau G (doubleConeBoundary M) (n + 1) :=
  ((nativeLoopSuspensionEquivOfReduced M b n hhigh hlow).trans
    (literalTwoConeDifferenceEquiv M
      (F (AddCommGrpCat.of G) (n + 2))).symm).trans
    (nativeThetaOfReduced (G := G) (doubleConeBoundary M)
      (none : Option (Option V)) (n + 1)
      (doubleConeBoundary_reducedCohomologyZeroAt_succ_of_reduced
        (G := G) M b n hlow)).symm

/-- The defining composition formula for (4.26). -/
@[simp]
theorem nativeSuspensionEquivOfReduced_apply
    (M : AbstractSimplicialComplex V) (b : V) (n : ℕ)
    (hhigh : ReducedCohomologyZeroAt (G := G) M b (n + 1))
    (hlow : ReducedCohomologyZeroAt (G := G) M b n)
    (x : SimplicialTPrime G M (n + 1)) :
    nativeSuspensionEquivOfReduced M b n hhigh hlow x =
      (nativeThetaOfReduced (G := G) (doubleConeBoundary M)
        (none : Option (Option V)) (n + 1)
        (doubleConeBoundary_reducedCohomologyZeroAt_succ_of_reduced
          (G := G) M b n hlow)).symm
        ((literalTwoConeDifferenceEquiv M
          (F (AddCommGrpCat.of G) (n + 2))).symm
          (nativeLoopSuspensionEquivOfReduced M b n hhigh hlow x)) :=
  rfl

/-- Applying `θ` and then the inner-minus-other difference to (4.26)
recovers the canonical transgression.  This is the choice-free
characterization of the composite. -/
@[simp]
theorem nativeSuspensionEquivOfReduced_characterization
    (M : AbstractSimplicialComplex V) (b : V) (n : ℕ)
    (hhigh : ReducedCohomologyZeroAt (G := G) M b (n + 1))
    (hlow : ReducedCohomologyZeroAt (G := G) M b n)
    (x : SimplicialTPrime G M (n + 1)) :
    literalTwoConeDifferenceEquiv M
        (F (AddCommGrpCat.of G) (n + 2))
        (nativeThetaOfReduced (G := G) (doubleConeBoundary M)
          (none : Option (Option V)) (n + 1)
          (doubleConeBoundary_reducedCohomologyZeroAt_succ_of_reduced
            (G := G) M b n hlow)
          (nativeSuspensionEquivOfReduced M b n hhigh hlow x)) =
      nativeLoopSuspensionEquivOfReduced M b n hhigh hlow x := by
  simp only [nativeSuspensionEquivOfReduced_apply,
    LinearEquiv.apply_symm_apply]

/-- Representative formula for (4.26): after applying `θ` and the
literal inner-minus-other difference, the class represented by `z` is
the canonical cone extension used in transgression. -/
theorem nativeSuspensionEquivOfReduced_mkQ_characterization
    (M : AbstractSimplicialComplex V) (b : V) (n : ℕ)
    (hhigh : ReducedCohomologyZeroAt (G := G) M b (n + 1))
    (hlow : ReducedCohomologyZeroAt (G := G) M b n)
    (z : Zprim (facetRestrictionData (G := G) M (n + 1))) :
    literalTwoConeDifferenceEquiv M
        (F (AddCommGrpCat.of G) (n + 2))
        (nativeThetaOfReduced (G := G) (doubleConeBoundary M)
          (none : Option (Option V)) (n + 1)
          (doubleConeBoundary_reducedCohomologyZeroAt_succ_of_reduced
            (G := G) M b n hlow)
          (nativeSuspensionEquivOfReduced M b n hhigh hlow
            ((BprimInZprim
              (facetRestrictionData (G := G) M (n + 1))).mkQ z))) =
      (canonicalConeCycleExtensionDataOfReduced
        (G := G) M b (n + 1) hhigh).nativeExtensionClass
          (M := M) (q := n + 1) z := by
  rw [nativeSuspensionEquivOfReduced_characterization,
    nativeLoopSuspensionEquivOfReduced_mkQ]

/-! ## The suspension comparison in paper degree one -/

/-- Formula (4.26) at `q = 1`.  The single visible assumption is exactly
the paper's `H~⁰(M;G)=0`; `H~⁰(ΣM;G)=0` is constructed internally from
the two cone edges and needs no hypothesis on the cohomology of `M`. -/
def nativeSuspensionEquivDegreeZero
    (M : AbstractSimplicialComplex V) (b : V)
    (hred : ReducedCohomologyZeroAt (G := G) M b 0) :
    SimplicialTPrime G M 0 ≃ₗ[ℤ]
      SimplicialTau G (doubleConeBoundary M) 0 :=
  ((nativeLoopSuspensionEquivDegreeZero M b hred).trans
    (literalTwoConeDifferenceEquiv M
      (F (AddCommGrpCat.of G) 1)).symm).trans
    (nativeThetaOfReduced (G := G) (doubleConeBoundary M)
      (none : Option (Option V)) 0
      (doubleConeBoundary_reducedCohomologyZeroAt_zero
        (G := G) M b)).symm

/-- The defining composition formula for the `q = 1` case of (4.26). -/
@[simp]
theorem nativeSuspensionEquivDegreeZero_apply
    (M : AbstractSimplicialComplex V) (b : V)
    (hred : ReducedCohomologyZeroAt (G := G) M b 0)
    (x : SimplicialTPrime G M 0) :
    nativeSuspensionEquivDegreeZero M b hred x =
      (nativeThetaOfReduced (G := G) (doubleConeBoundary M)
        (none : Option (Option V)) 0
        (doubleConeBoundary_reducedCohomologyZeroAt_zero
          (G := G) M b)).symm
        ((literalTwoConeDifferenceEquiv M
          (F (AddCommGrpCat.of G) 1)).symm
          (nativeLoopSuspensionEquivDegreeZero M b hred x)) :=
  rfl

/-- Applying `θ` and inner-minus-other to the low suspension comparison
recovers the degree-zero transgression. -/
@[simp]
theorem nativeSuspensionEquivDegreeZero_characterization
    (M : AbstractSimplicialComplex V) (b : V)
    (hred : ReducedCohomologyZeroAt (G := G) M b 0)
    (x : SimplicialTPrime G M 0) :
    literalTwoConeDifferenceEquiv M
        (F (AddCommGrpCat.of G) 1)
        (nativeThetaOfReduced (G := G) (doubleConeBoundary M)
          (none : Option (Option V)) 0
          (doubleConeBoundary_reducedCohomologyZeroAt_zero
            (G := G) M b)
          (nativeSuspensionEquivDegreeZero M b hred x)) =
      nativeLoopSuspensionEquivDegreeZero M b hred x := by
  simp only [nativeSuspensionEquivDegreeZero_apply,
    LinearEquiv.apply_symm_apply]

/-- Representative formula for the `q = 1` suspension comparison. -/
theorem nativeSuspensionEquivDegreeZero_mkQ_characterization
    (M : AbstractSimplicialComplex V) (b : V)
    (hred : ReducedCohomologyZeroAt (G := G) M b 0)
    (z : Zprim (facetRestrictionData (G := G) M 0)) :
    literalTwoConeDifferenceEquiv M
        (F (AddCommGrpCat.of G) 1)
        (nativeThetaOfReduced (G := G) (doubleConeBoundary M)
          (none : Option (Option V)) 0
          (doubleConeBoundary_reducedCohomologyZeroAt_zero
            (G := G) M b)
          (nativeSuspensionEquivDegreeZero M b hred
            ((BprimInZprim
              (facetRestrictionData (G := G) M 0)).mkQ z))) =
      (canonicalConeCycleExtensionDataOfReduced
        (G := G) M b 0 hred).nativeExtensionClass
          (M := M) (q := 0) z := by
  rw [nativeSuspensionEquivDegreeZero_characterization,
    nativeLoopSuspensionEquivDegreeZero_mkQ]

/-! ## The oriented-sphere presentation of (4.27) -/

/-- If `X` has been chosen as an oriented simplicial `d`-sphere, this
native pointed mapping-class group is the definition/presentation of
`π_d(A)`.  The dimension and orientation are properties of that chosen
presentation: they do not require an additional placeholder structure in
the Lean statement, and reversing the external orientation changes the
resulting evaluation by a sign. -/
abbrev OrientedSpherePiPresentation
    {W : Type u} [LinearOrder W]
    (X : AbstractSimplicialComplex W) (b : W)
    (A : SimplicialObject AddCommGrpCat.{u}) :=
  NativeHomotopyClass (orderedComplexBasepointSubcomplex X b) A

/-- For an oriented simplicial `d`-sphere `X`, the cone-quotient model is
the definition/presentation of `[X, ΩA]_* = π_d(ΩA) = π_{d+1}(A)` used in
the second line of (4.27). -/
abbrev OrientedSphereLoopPiPresentation
    {W : Type u} [LinearOrder W]
    (X : AbstractSimplicialComplex W)
    (A : SimplicialObject AddCommGrpCat.{u}) :=
  NativeConeQuotientHomotopyClasses X A

/-!
These two aliases record the standard definition used in the paper; this
module does not claim a separately formalized equivalence for every
triangulated oriented sphere.  Consequently the native mapping-class
arrows below and the algebraic Dold--Kan homotopy--homology arrows at the
end are intentionally not joined by a fabricated intermediate isomorphism.
-/

/-- The first mapping-class arrow in the sphere corollary, before reading
the target presentation as `π_d(F)`. -/
def nativeSphereTauPiPresentationOfReduced
    (X : AbstractSimplicialComplex V) (b : V) (q : ℕ)
    (hred : ReducedCohomologyZeroAt (G := G) X b q) :
    SimplicialTau G X q ≃ₗ[ℤ]
      OrientedSpherePiPresentation X b
        (F (AddCommGrpCat.of G) (q + 1)) :=
  nativeThetaOfReduced X b q hred

/-- The second mapping-class arrow in the sphere corollary in paper
degrees at least two, before reading the target presentation as
`π_d(ΩF)`. -/
def nativeSphereTPrimeLoopPiPresentationOfReduced
    (X : AbstractSimplicialComplex V) (b : V) (n : ℕ)
    (hhigh : ReducedCohomologyZeroAt (G := G) X b (n + 1))
    (hlow : ReducedCohomologyZeroAt (G := G) X b n) :
    SimplicialTPrime G X (n + 1) ≃ₗ[ℤ]
      OrientedSphereLoopPiPresentation X
        (F (AddCommGrpCat.of G) (n + 2)) :=
  nativeLoopSuspensionEquivOfReduced X b n hhigh hlow

/-- The second mapping-class arrow in (4.27) at paper degree `q = 1`. -/
def nativeSphereTPrimeLoopPiPresentationDegreeZeroOfReduced
    (X : AbstractSimplicialComplex V) (b : V)
    (hred : ReducedCohomologyZeroAt (G := G) X b 0) :
    SimplicialTPrime G X 0 ≃ₗ[ℤ]
      OrientedSphereLoopPiPresentation X
        (F (AddCommGrpCat.of G) 1) :=
  nativeLoopSuspensionEquivDegreeZero X b hred

/-- The unconditional final arrow in the first line of (4.27), after the
oriented-sphere presentation has been read as `π_d(F(G,q+1))`. -/
abbrev standardSphereFiberPiHomologyIso
    (q d : ℕ) :=
  standardFiberHomotopyReducedHomologyIso
    (AddCommGrpCat.of G) q d

/-- The unconditional final arrow in the second line of (4.27): use
`π_d(ΩF) = π_{d+1}(F)` and then the same standard homology shift. -/
abbrev standardSphereLoopFiberPiHomologyIso
    (q d : ℕ) :=
  standardFiberHomotopyReducedHomologyIso
    (AddCommGrpCat.of G) q (d + 1)

end GeneralSphereT.SimplicialCochain
