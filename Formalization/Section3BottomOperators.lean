import Formalization.ClosedPrimitiveImage
import Formalization.PrimitiveQuotientFunctoriality
import Formalization.Section3SimultaneousReplacement

set_option linter.style.header false

/-!
# Section 3: paths whose operators lie in the bottom submodule

This file isolates the last, purely algebraic, step in the cone argument.
Suppose a submodule `C₀` of configurations maps isomorphically to the physical
configuration group: we only name an injective restriction of `d` and a
facet-compatible right inverse.  A physical path all of whose complete
elementary labels lie in `C₀` can then be lifted by applying the right inverse
to its base points and leaving its operator labels unchanged.

The key point is closedness.  The lifted path comes from a path entirely in
`C₀`; naturality of the boundary and injectivity of `d | C₀` therefore turn
physical closedness into primitive closedness.  The already formalized
closed-elementary-local-zero theorem then puts the original physical path in
`E_id`.
-/

noncomputable section

namespace GeneralSphereT.PathAlgebra

universe uF uB uBA

variable {ι G B : Type*}
variable [LinearOrder ι] [AddCommGroup G] [AddCommGroup B]
variable {Facet : Type uF}
variable {facets : Facet → Set ι}
variable {BAt : Facet → Type uBA} [∀ ρ, AddCommGroup (BAt ρ)]
variable {d : Configuration ι G →+ B}

private abbrev ConeConfig := Configuration ι G

variable {L : FacetRestrictionData
  (CAt := fun ρ => Configuration (facets ρ) G)
  (BAt := BAt) (Facet := Facet) d}

/-- The additive inclusion of a bottom submodule into all configurations. -/
def bottomInclusion (C₀ : Submodule ℤ (ConeConfig (ι := ι) (G := G))) :
    C₀ →+ ConeConfig (ι := ι) (G := G) :=
  C₀.subtype.toAddMonoidHom

/--
Data needed to lift physical base points into the bottom submodule.

The local sections are used only to transport facetwise vanishing.  No
left-inverse equation is imposed on them.  Globally, injectivity of `d | C₀`
is the exact hypothesis used in the boundary argument.
-/
structure BottomSectionData
    (C₀ : Submodule ℤ (ConeConfig (ι := ι) (G := G))) where
  baseSection : B →+ C₀
  rightInverse :
    (d.comp (bottomInclusion C₀)).comp baseSection = AddMonoidHom.id B
  injectiveOnBottom : Function.Injective (d.comp (bottomInclusion C₀))
  localSection : ∀ ρ : Facet, BAt ρ →+ Configuration (facets ρ) G
  restrict_section : ∀ ρ : Facet,
    (L.primitiveRes ρ).comp ((bottomInclusion C₀).comp baseSection) =
      (localSection ρ).comp (L.physicalRes ρ)

namespace BottomSectionData

variable {C₀ : Submodule ℤ (ConeConfig (ι := ι) (G := G))}

/-- The global bottom section, with its codomain coerced back to `C`. -/
def sectionInto (A : BottomSectionData (L := L) C₀) :
    B →+ ConeConfig (ι := ι) (G := G) :=
  (bottomInclusion C₀).comp A.baseSection

omit [LinearOrder ι] in
@[simp]
theorem d_sectionInto (A : BottomSectionData (L := L) C₀) (a : B) :
    d (A.sectionInto a) = a := by
  exact DFunLike.congr_fun A.rightInverse a

/-- Lift physical base points and leave every complete operator label fixed. -/
def liftPath (A : BottomSectionData (L := L) C₀) :
    Path (ConeConfig (ι := ι) (G := G)) B →ₗ[ℤ]
      Path (ConeConfig (ι := ι) (G := G)) (ConeConfig (ι := ι) (G := G)) :=
  mapPath (AddMonoidHom.id _) A.sectionInto

omit [LinearOrder ι] in
@[simp]
theorem liftPath_edge (A : BottomSectionData (L := L) C₀)
    (r : ConeConfig (ι := ι) (G := G)) (a : B) :
    A.liftPath (edge r a) = edge r (A.sectionInto a) := by
  simp [liftPath]

omit [LinearOrder ι] in
/-- Applying `d_*` to the lifted path returns the original physical path. -/
theorem mapDPath_liftPath (A : BottomSectionData (L := L) C₀)
    (e : Path (ConeConfig (ι := ι) (G := G)) B) :
    mapDPath d (A.liftPath e) = e := by
  calc
    mapDPath d (A.liftPath e) =
        mapPath (AddMonoidHom.id _)
          (d.comp A.sectionInto) e := by
      simpa [liftPath] using
        mapPath_comp_apply (AddMonoidHom.id _)
          A.sectionInto (AddMonoidHom.id _) d e
    _ = mapPath (AddMonoidHom.id _) (AddMonoidHom.id _) e := by
      rw [show d.comp A.sectionInto = AddMonoidHom.id B from
        A.rightInverse]
    _ = e := mapPath_id_apply e

omit [LinearOrder ι] in
/-- Facet restriction of the lift is obtained by applying the local section
to the restricted physical path. -/
theorem restrictPrimitivePath_liftPath
    (A : BottomSectionData (L := L) C₀) (ρ : Facet)
    (e : Path (ConeConfig (ι := ι) (G := G)) B) :
    L.restrictPrimitivePath ρ (A.liftPath e) =
      mapPath (AddMonoidHom.id _) (A.localSection ρ)
        (L.restrictPhysicalPath ρ e) := by
  calc
    L.restrictPrimitivePath ρ (A.liftPath e) =
        mapPath (L.primitiveRes ρ)
          ((L.primitiveRes ρ).comp A.sectionInto) e := by
      simpa [FacetRestrictionData.restrictPrimitivePath, liftPath] using
        mapPath_comp_apply (AddMonoidHom.id _)
          A.sectionInto (L.primitiveRes ρ) (L.primitiveRes ρ) e
    _ = mapPath (L.primitiveRes ρ)
          ((A.localSection ρ).comp (L.physicalRes ρ)) e := by
      rw [show (L.primitiveRes ρ).comp A.sectionInto =
          (A.localSection ρ).comp (L.physicalRes ρ) by
        simpa [sectionInto] using A.restrict_section ρ]
    _ = mapPath (AddMonoidHom.id _) (A.localSection ρ)
          (L.restrictPhysicalPath ρ e) := by
      symm
      simpa [FacetRestrictionData.restrictPhysicalPath] using
        mapPath_comp_apply (L.primitiveRes ρ) (L.physicalRes ρ)
          (AddMonoidHom.id _) (A.localSection ρ) e

omit [LinearOrder ι] in
/-- A locally zero physical path has a locally zero bottom lift. -/
theorem liftPath_mem_locallyZero
    (A : BottomSectionData (L := L) C₀)
    {e : Path (ConeConfig (ι := ι) (G := G)) B}
    (he : e ∈ L.locallyZeroPhysicalPath) :
    A.liftPath e ∈ L.locallyZeroPrimitivePath := by
  rw [FacetRestrictionData.locallyZeroPrimitivePath, Submodule.mem_iInf]
  intro ρ
  change L.restrictPrimitivePath ρ (A.liftPath e) = 0
  rw [A.restrictPrimitivePath_liftPath]
  have hρ : L.restrictPhysicalPath ρ e = 0 :=
    (Submodule.mem_iInf (fun σ : Facet =>
      LinearMap.ker (L.restrictPhysicalPath σ))).1 he ρ
  simp [hρ]

omit [LinearOrder ι] in
/-- Changing only base points preserves elementary operator labels. -/
theorem liftPath_mem_elementary
    (A : BottomSectionData (L := L) C₀)
    {e : Path (ConeConfig (ι := ι) (G := G)) B}
    (he : e ∈ elementaryPaths (ι := ι) (G := G) (X := B)) :
    A.liftPath e ∈ elementaryPaths
      (ι := ι) (G := G) (X := ConeConfig (ι := ι) (G := G)) := by
  change e ∈ Submodule.span ℤ
    {p | ∃ (i : ι) (g : G) (x : B),
      g ≠ 0 ∧ p = edge (Finsupp.single i g) x} at he
  induction he using Submodule.span_induction with
  | mem p hp =>
      rcases hp with ⟨i, g, a, hg, rfl⟩
      rw [liftPath_edge]
      exact elementaryEdge_mem i hg (A.sectionInto a)
  | zero => simp
  | add p q hp hq ihp ihq =>
      simpa using (elementaryPaths
        (ι := ι) (G := G) (X := ConeConfig (ι := ι) (G := G))).add_mem ihp ihq
  | smul n p hp ih =>
      simpa using (elementaryPaths
        (ι := ι) (G := G) (X := ConeConfig (ι := ι) (G := G))).smul_mem n ih

omit [LinearOrder ι] in
/--
If all complete labels lie in `C₀`, the lifted path actually comes from a
path whose increments and bases are both typed in `C₀`.  This is the precise
Lean substitute for saying that the primitive boundary is supported in the
bottom.
-/
theorem exists_bottom_path
    (A : BottomSectionData (L := L) C₀)
    {e : Path (ConeConfig (ι := ι) (G := G)) B}
    (he : e ∈ restrictedElementaryPaths (B := B) (fun r => r ∈ C₀)) :
    ∃ U₀ : Path C₀ C₀,
      mapPath (bottomInclusion C₀) (bottomInclusion C₀) U₀ =
        A.liftPath e := by
  change e ∈ Submodule.span ℤ
    {p | ∃ (r : ConeConfig (ι := ι) (G := G)) (a : B),
      IsElementaryLabel r ∧ r ∈ C₀ ∧ p = edge r a} at he
  induction he using Submodule.span_induction with
  | mem p hp =>
      rcases hp with ⟨r, a, hr, hrC₀, rfl⟩
      refine ⟨edge (⟨r, hrC₀⟩ : C₀) (A.baseSection a), ?_⟩
      simp [liftPath, sectionInto, bottomInclusion]
  | zero => exact ⟨0, by simp [liftPath]⟩
  | add p q hp hq ihp ihq =>
      rcases ihp with ⟨P, hP⟩
      rcases ihq with ⟨Q, hQ⟩
      refine ⟨P + Q, ?_⟩
      simp only [map_add]
      rw [hP, hQ]
  | smul n p hp ih =>
      rcases ih with ⟨P, hP⟩
      refine ⟨n • P, ?_⟩
      simp [hP]

omit [LinearOrder ι] in
/-- An injective map on generators induces an injective map on finite
integral distributions. -/
theorem mapDist_injective_of_injective
    {X Y : Type*} [AddCommGroup X] [AddCommGroup Y]
    (f : X →+ Y) (hf : Function.Injective f) :
    Function.Injective (mapDist f) := by
  intro u v huv
  exact Finsupp.mapDomain_injective hf huv

omit [LinearOrder ι] in
/--
Boundary-injectivity core.  Physical closedness of a bottom-labelled path
forces the primitive lift to be closed; no induction on support is used.
-/
theorem primitiveBoundary_liftPath_eq_zero
    (A : BottomSectionData (L := L) C₀)
    {e : Path (ConeConfig (ι := ι) (G := G)) B}
    (hlabels : e ∈
      restrictedElementaryPaths (B := B) (fun r => r ∈ C₀))
    (hclosed : configurationBoundary d e = 0) :
    primitiveBoundary (ConeConfig (ι := ι) (G := G)) (A.liftPath e) = 0 := by
  obtain ⟨U₀, hU₀⟩ := A.exists_bottom_path hlabels
  let ι₀ : C₀ →+ ConeConfig (ι := ι) (G := G) := bottomInclusion C₀
  let d₀ : C₀ →+ B := d.comp ι₀
  have hboundaryIncl :
      primitiveBoundary (ConeConfig (ι := ι) (G := G))
          (mapPath ι₀ ι₀ U₀) =
        mapDist ι₀ (primitiveBoundary C₀ U₀) := by
    symm
    exact LinearMap.congr_fun
      (boundary_natural (AddMonoidHom.id C₀)
        (AddMonoidHom.id (ConeConfig (ι := ι) (G := G))) ι₀ ι₀ (by ext x; rfl)) U₀
  have hmapBoundary :
      mapDist d₀ (primitiveBoundary C₀ U₀) = 0 := by
    calc
      mapDist d₀ (primitiveBoundary C₀ U₀) =
          mapDist d (mapDist ι₀ (primitiveBoundary C₀ U₀)) := by
        symm
        exact mapDist_comp_apply ι₀ d (primitiveBoundary C₀ U₀)
      _ = mapDist d
          (primitiveBoundary (ConeConfig (ι := ι) (G := G)) (A.liftPath e)) := by
        rw [← hboundaryIncl, hU₀]
      _ = configurationBoundary d (mapDPath d (A.liftPath e)) :=
        LinearMap.congr_fun (mapD_boundary d) (A.liftPath e)
      _ = configurationBoundary d e := by rw [A.mapDPath_liftPath]
      _ = 0 := hclosed
  have hboundary₀ : primitiveBoundary C₀ U₀ = 0 := by
    apply mapDist_injective_of_injective d₀
      (by simpa [d₀, ι₀] using A.injectiveOnBottom)
    simpa using hmapBoundary
  calc
    primitiveBoundary (ConeConfig (ι := ι) (G := G)) (A.liftPath e) =
        primitiveBoundary (ConeConfig (ι := ι) (G := G))
          (mapPath ι₀ ι₀ U₀) := by rw [hU₀]
    _ = mapDist ι₀ (primitiveBoundary C₀ U₀) := hboundaryIncl
    _ = 0 := by simp [hboundary₀]

end BottomSectionData

/-!
## The bottom-operator conclusion
-/

/--
The complete abstract lemma for the ``only bottom operators remain'' case.
It consumes an element of `E_inv` whose complete elementary labels lie in
`C₀`, constructs the closed elementary locally-zero primitive lift above, and
then invokes the Section 2 closed-image theorem to conclude membership in
`E_id`.
-/
theorem mem_physicalIdentityPaths_of_labels_mem_bottom
    (C₀ : Submodule ℤ (ConeConfig (ι := ι) (G := G)))
    (A : BottomSectionData (L := L) C₀)
    (hprimitive : ∀ ρ : Facet,
      L.primitiveRes ρ = coordinateRestriction (facets ρ))
    (hcover : ∀ i : ι, ∃ ρ : Facet, i ∈ facets ρ)
    {e : Path (ConeConfig (ι := ι) (G := G)) B}
    (he : e ∈ physicalInvariantPaths L)
    (hlabels : e ∈
      restrictedElementaryPaths (B := B) (fun r => r ∈ C₀)) :
    e ∈ physicalIdentityPaths L := by
  have hphysicalClosed : configurationBoundary d e = 0 := by
    have hred := LinearMap.mem_ker.mp he.2.1
    exact congrArg Subtype.val hred
  have helemLift : A.liftPath e ∈ elementaryPaths
      (ι := ι) (G := G) (X := ConeConfig (ι := ι) (G := G)) :=
    A.liftPath_mem_elementary he.1
  have hclosedLift :
      primitiveReducedBoundary (ConeConfig (ι := ι) (G := G))
          (A.liftPath e) = 0 := by
    apply Subtype.ext
    exact A.primitiveBoundary_liftPath_eq_zero hlabels hphysicalClosed
  have hlocalLift : A.liftPath e ∈ L.locallyZeroPrimitivePath :=
    A.liftPath_mem_locallyZero he.2.2
  have himage :=
    mapDPath_mem_physicalIdentityPaths_of_closed_elementary_locallyZero
      facets L hprimitive hcover helemLift hclosedLift hlocalLift
  rw [A.mapDPath_liftPath] at himage
  exact himage

end GeneralSphereT.PathAlgebra
