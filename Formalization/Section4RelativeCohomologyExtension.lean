import Formalization.Section4CocycleExtension
import Formalization.Section4CochainExtensionByZero

set_option linter.style.header false

/-!
# Section 4: relative cohomology gives the fibrewise extension

This file turns the relative-cohomology hypothesis used in (4.7) into an
ordinary equality of submodules.  For an ordered simplicial embedding
`A → Z`, relative cochains are the kernel of restriction.  Vanishing of
relative cohomology in degree `n + 1` is expressed by

`range (d : C^n(Z,A) → C^{n+1}(Z,A)) =
  ker (d : C^{n+1}(Z,A) → C^{n+2}(Z,A))`.

From this equality we prove the extension statement (4.7) directly.  Taking
the prescribed global cocycle to be zero then constructs the
`CocycleExtensionData` required by the fibrewise argument, and hence the
actual lift (4.9).  Thus neither cocycle extension nor fibrewise lifting is
left as an additional field.
-/

noncomputable section

namespace GeneralSphereT.SimplicialCochain

open GeneralSphereT.PathAlgebra
open GeneralSphereT.PathAlgebra.FacetRestrictionData

universe uV uW

variable {V : Type uV} {W : Type uW}
variable [LinearOrder V] [LinearOrder W] [Fintype V] [Fintype W]
variable {G : Type*} [AddCommGroup G]
variable {A : AbstractSimplicialComplex V}
variable {Z : AbstractSimplicialComplex W}

namespace OrderedSimplicialMap

/-- Relative cochains for an ordered simplicial embedding are cochains whose
restriction to the subcomplex is zero. -/
abbrev RelativeCochain (F : OrderedSimplicialMap A Z) (n : ℕ) :=
  LinearMap.ker (F.pullback (G := G) n)

/-- The simplicial coboundary restricted to relative cochains. -/
def relativeCoboundary (F : OrderedSimplicialMap A Z) (n : ℕ) :
    RelativeCochain (G := G) F n →ₗ[ℤ]
      RelativeCochain (G := G) F (n + 1) :=
  LinearMap.codRestrict (RelativeCochain (G := G) F (n + 1))
    ((coboundary Z n).comp
      (RelativeCochain (G := G) F n).subtype) fun c => by
        rw [LinearMap.mem_ker]
        have hnat := LinearMap.congr_fun
          (F.pullback_coboundary (G := G) n) c.1
        have hnat' :
            F.pullback (n + 1) (coboundary Z n c.1) =
              coboundary A n (F.pullback n c.1) := by
          simpa using hnat
        change F.pullback (n + 1) (coboundary Z n c.1) = 0
        rw [hnat', c.2]
        simp

@[simp]
theorem relativeCoboundary_coe (F : OrderedSimplicialMap A Z) (n : ℕ)
    (c : RelativeCochain (G := G) F n) :
    ((F.relativeCoboundary (G := G) n c :
        RelativeCochain (G := G) F (n + 1)) : Cochain Z (n + 1) G) =
      coboundary Z n c.1 :=
  rfl

/-- The relative coboundary still squares to zero. -/
@[simp]
theorem relativeCoboundary_relativeCoboundary
    (F : OrderedSimplicialMap A Z) (n : ℕ)
    (c : RelativeCochain (G := G) F n) :
    F.relativeCoboundary (G := G) (n + 1)
        (F.relativeCoboundary n c) = 0 := by
  apply Subtype.ext
  exact coboundary_coboundary Z n c.1

/-- `H^{n+1}(Z,A;G) = 0`, stated without introducing a quotient cohomology
group: every relative `(n+1)`-cocycle is a relative coboundary. -/
def RelativeCohomologyZeroAtSucc
    (F : OrderedSimplicialMap A Z) (n : ℕ) : Prop :=
  LinearMap.range (F.relativeCoboundary (G := G) n) =
    LinearMap.ker (F.relativeCoboundary (G := G) (n + 1))

/-- The concrete relative extension lemma (4.7).  First extend `c` by zero.
The difference `β - d(c⁺)` is a relative cocycle; relative exactness writes it
as `da`, and `c⁺ + a` is the desired extension. -/
theorem exists_extension_with_coboundary
    (F : OrderedSimplicialMap A Z) (n : ℕ)
    (hrel : RelativeCohomologyZeroAtSucc (G := G) F n)
    (c : Cochain A n G) (β : Cochain Z (n + 1) G)
    (hβcycle : coboundary Z (n + 1) β = 0)
    (hβres : F.pullback (n + 1) β = coboundary A n c) :
    ∃ cHat : Cochain Z n G,
      F.pullback n cHat = c ∧ coboundary Z n cHat = β := by
  let cPlus : Cochain Z n G := F.extendCochainByZero n c
  let γ : RelativeCochain (G := G) F (n + 1) :=
    ⟨β - coboundary Z n cPlus, by
      rw [LinearMap.mem_ker]
      change F.pullback (n + 1) (β - coboundary Z n cPlus) = 0
      rw [map_sub, hβres]
      have hnat := LinearMap.congr_fun
        (F.pullback_coboundary (G := G) n) cPlus
      have hnat' :
          F.pullback (n + 1) (coboundary Z n cPlus) =
            coboundary A n (F.pullback n cPlus) := by
        simpa using hnat
      rw [hnat']
      change coboundary A n c -
        coboundary A n (F.pullback n cPlus) = 0
      rw [show F.pullback n cPlus = c by
        exact F.pullback_extendCochainByZero n c]
      exact sub_self _⟩
  have hγcycle : F.relativeCoboundary (G := G) (n + 1) γ = 0 := by
    apply Subtype.ext
    change coboundary Z (n + 1) (β - coboundary Z n cPlus) = 0
    rw [map_sub, hβcycle, coboundary_coboundary, sub_zero]
  have hγker : γ ∈ LinearMap.ker
      (F.relativeCoboundary (G := G) (n + 1)) := by
    exact hγcycle
  rw [← hrel] at hγker
  rcases hγker with ⟨a, ha⟩
  refine ⟨cPlus + a.1, ?_, ?_⟩
  · rw [map_add, a.2, add_zero]
    exact F.pullback_extendCochainByZero n c
  · rw [map_add]
    have ha' : coboundary Z n a.1 = β - coboundary Z n cPlus :=
      congrArg Subtype.val ha
    rw [ha']
    abel

/-- A chosen instance of (4.7), useful when later constructions need an
actual function rather than only existence. -/
def extensionWithCoboundary
    (F : OrderedSimplicialMap A Z) (n : ℕ)
    (hrel : RelativeCohomologyZeroAtSucc (G := G) F n)
    (c : Cochain A n G) (β : Cochain Z (n + 1) G)
    (hβcycle : coboundary Z (n + 1) β = 0)
    (hβres : F.pullback (n + 1) β = coboundary A n c) :
    Cochain Z n G :=
  Classical.choose
    (F.exists_extension_with_coboundary n hrel c β hβcycle hβres)

@[simp]
theorem pullback_extensionWithCoboundary
    (F : OrderedSimplicialMap A Z) (n : ℕ)
    (hrel : RelativeCohomologyZeroAtSucc (G := G) F n)
    (c : Cochain A n G) (β : Cochain Z (n + 1) G)
    (hβcycle : coboundary Z (n + 1) β = 0)
    (hβres : F.pullback (n + 1) β = coboundary A n c) :
    F.pullback n
        (F.extensionWithCoboundary n hrel c β hβcycle hβres) = c :=
  (Classical.choose_spec
    (F.exists_extension_with_coboundary n hrel c β hβcycle hβres)).1

@[simp]
theorem coboundary_extensionWithCoboundary
    (F : OrderedSimplicialMap A Z) (n : ℕ)
    (hrel : RelativeCohomologyZeroAtSucc (G := G) F n)
    (c : Cochain A n G) (β : Cochain Z (n + 1) G)
    (hβcycle : coboundary Z (n + 1) β = 0)
    (hβres : F.pullback (n + 1) β = coboundary A n c) :
    coboundary Z n
        (F.extensionWithCoboundary n hrel c β hβcycle hβres) = β :=
  (Classical.choose_spec
    (F.exists_extension_with_coboundary n hrel c β hβcycle hβres)).2

/-- Relative cohomology vanishing therefore extends every source cocycle to
a target cocycle.  This is the precise input previously packaged as
`CocycleExtensionData`. -/
def cocycleExtensionDataOfRelativeCohomology
    (F : OrderedSimplicialMap A Z) (n : ℕ)
    (hrel : RelativeCohomologyZeroAtSucc (G := G) F n) :
    CocycleExtensionData
      (coboundaryToRange (G := G) A n)
      (coboundaryToRange (G := G) Z n)
      (F.pullback (G := G) n).toAddMonoidHom where
  extend z := by
    have hdc : coboundary A n z.1 = 0 :=
      congrArg Subtype.val z.2
    exact F.extensionWithCoboundary n hrel z.1 0 (by simp) (by simp [hdc])
  res_extend z := by
    have hdc : coboundary A n z.1 = 0 :=
      congrArg Subtype.val z.2
    exact F.pullback_extensionWithCoboundary n hrel z.1 0
      (by simp) (by simp [hdc])
  d_extend z := by
    apply Subtype.ext
    have hdc : coboundary A n z.1 = 0 :=
      congrArg Subtype.val z.2
    exact F.coboundary_extensionWithCoboundary n hrel z.1 0
      (by simp) (by simp [hdc])

/-- Equation (4.9), constructed from the range/kernel form of relative
cohomology vanishing.  The unrestricted extension is the concrete
extension-by-zero map, while the cocycle correction is supplied by (4.7). -/
def fiberwiseCochainLiftOfRelativeCohomology
    (F : OrderedSimplicialMap A Z) (n : ℕ)
    (hrel : RelativeCohomologyZeroAtSucc (G := G) F n) :
    FiberwiseCochainLift
      (coboundaryToRange (G := G) A n)
      (coboundaryToRange (G := G) Z n)
      (F.pullback (G := G) n).toAddMonoidHom :=
  FiberwiseCochainLift.ofCocycleExtension
    (coboundaryToRange_surjective (G := G) A n)
    (F.extendCochainByZero n)
    (F.pullback_extendCochainByZero n)
    (F.cocycleExtensionDataOfRelativeCohomology n hrel)

@[simp]
theorem fiberwiseCochainLiftOfRelativeCohomology_res
    (F : OrderedSimplicialMap A Z) (n : ℕ)
    (hrel : RelativeCohomologyZeroAtSucc (G := G) F n)
    (c : Cochain A n G) :
    F.pullback n
        ((F.fiberwiseCochainLiftOfRelativeCohomology n hrel).lift c) = c :=
  (F.fiberwiseCochainLiftOfRelativeCohomology n hrel).res_lift c

/-- The second half of (4.9): the coboundary of the chosen lift depends only
on the original coboundary fibre. -/
theorem fiberwiseCochainLiftOfRelativeCohomology_coboundary
    (F : OrderedSimplicialMap A Z) (n : ℕ)
    (hrel : RelativeCohomologyZeroAtSucc (G := G) F n)
    (c : Cochain A n G) :
    coboundaryToRange (G := G) Z n
        ((F.fiberwiseCochainLiftOfRelativeCohomology n hrel).lift c) =
      (F.fiberwiseCochainLiftOfRelativeCohomology n hrel).physicalLift
        (coboundaryToRange (G := G) A n c) :=
  (F.fiberwiseCochainLiftOfRelativeCohomology n hrel).d_lift c

/-- The group-homomorphic section on primitive relations asserted in the
unpointed part of Lemma 4.2.  It is now a consequence, rather than an input,
of the relative `range = ker` hypothesis. -/
def primitiveRelationSectionOfRelativeCohomology
    (F : OrderedSimplicialMap A Z) (n : ℕ)
    (hrel : RelativeCohomologyZeroAtSucc (G := G) F n) :
    Rprim (d := coboundaryToRange (G := G) A n) →ₗ[ℤ]
      Rprim (d := coboundaryToRange (G := G) Z n) :=
  (F.fiberwiseCochainLiftOfRelativeCohomology n hrel).relationSection

/-- Restricting the primitive relation section recovers the original
relation exactly. -/
@[simp]
theorem mapRedDist_primitiveRelationSectionOfRelativeCohomology
    (F : OrderedSimplicialMap A Z) (n : ℕ)
    (hrel : RelativeCohomologyZeroAtSucc (G := G) F n)
    (r : Rprim (d := coboundaryToRange (G := G) A n)) :
    mapRedDist (F.pullback (G := G) n).toAddMonoidHom
        (F.primitiveRelationSectionOfRelativeCohomology n hrel r).1 = r.1 :=
  FiberwiseCochainLift.mapRedDist_relationSection
    (F.fiberwiseCochainLiftOfRelativeCohomology n hrel) r

end OrderedSimplicialMap

end GeneralSphereT.SimplicialCochain
