import Formalization.Transport.Simplicial
import Formalization.SimplicialMaximalFacetPresentation
import Formalization.SimplicialPhysicalPrimitiveComparison

noncomputable section
namespace GeneralSphereT.Transport
open GeneralSphereT.PathAlgebra GeneralSphereT.PathAlgebra.FacetRestrictionData
open GeneralSphereT.SimplicialCochain OpenDisk.PhaseDuality
variable {V G : Type*} [LinearOrder V] [Fintype V] [AddCommGroup G]
variable (K : AbstractSimplicialComplex V) (d n : ℕ)

/-- Purity is expressed by the dimensions of the actual maximal faces. -/
def PureInDimension := ∀ μ : MaximalFacet K, μ.val.val.card = d+1

def topRelativeSections : RelativePrimitiveSectionData
    (fun σ : Simplex K d => facesIn K n ⟨σ.val,σ.property.1⟩) (topFacetData (G:=G) K d n) where
  globalPrimitive := (simplicialRelativePrimitiveSectionData (G:=G) K n).globalPrimitive
  map_globalPrimitive := (simplicialRelativePrimitiveSectionData (G:=G) K n).map_globalPrimitive
  localPrimitive σ := (simplicialRelativePrimitiveSectionData (G:=G) K n).localPrimitive ⟨σ.val,σ.property.1⟩
  restrict_globalPrimitive σ := (simplicialRelativePrimitiveSectionData (G:=G) K n).restrict_globalPrimitive
    ⟨σ.val,σ.property.1⟩

theorem topCover (hp : PureInDimension K d) (v : Cochain K n G)
    (hv : ∀ i, (topFacetData K d n).primitiveRes i v = 0) : v=0 := by
  ext η
  obtain ⟨μ,hμ⟩ := maximalFacetRestrictionData_cover K n η
  let σ : Simplex K d := ⟨μ.val.val,μ.val.property,hp μ⟩
  exact DFunLike.congr_fun (hv σ) ⟨η,hμ⟩

theorem topPrimitiveSubmodules (hp : PureInDimension K d) :
    Zprim (topFacetData (G:=G) K d n)=Zprim (facetRestrictionData (G:=G) K n) ∧
    Bprim (topFacetData (G:=G) K d n)=Bprim (facetRestrictionData (G:=G) K n) := by
  let T := topFacetData (G:=G) K d n
  let L := facetRestrictionData (G:=G) K n
  have paths : locallyZeroPrimitivePath T = locallyZeroPrimitivePath L := by
    apply le_antisymm
    · rw [← locallyZeroPrimitivePath_maximal_eq_all]
      intro p h
      apply (Submodule.mem_iInf _).mpr
      intro μ
      let σ : Simplex K d := ⟨μ.val.val,μ.val.property,hp μ⟩
      exact (Submodule.mem_iInf (fun i => LinearMap.ker (restrictPrimitivePath T i))).mp h σ
    · intro p h
      apply (Submodule.mem_iInf _).mpr
      intro σ
      exact (Submodule.mem_iInf (fun i => LinearMap.ker (restrictPrimitivePath L i))).mp h
        ⟨σ.val,σ.property.1⟩
  have red : locallyZeroRedDist T = locallyZeroRedDist L := by
    apply le_antisymm
    · rw [← locallyZeroRedDist_maximal_eq_all]
      intro p h
      apply (Submodule.mem_iInf _).mpr
      intro μ
      let σ : Simplex K d := ⟨μ.val.val,μ.val.property,hp μ⟩
      exact (Submodule.mem_iInf (fun i => LinearMap.ker (restrictRedDist T i))).mp h σ
    · intro p h
      apply (Submodule.mem_iInf _).mpr
      intro σ
      exact (Submodule.mem_iInf (fun i => LinearMap.ker (restrictRedDist L i))).mp h
        ⟨σ.val,σ.property.1⟩
  have z : Zprim T = Zprim L := by simp only [Zprim,red]
  have b : Bprim T = Bprim L := by simp only [Bprim,relationPaths,paths]
  exact ⟨z,b⟩

private def reindex {U : Type*} [AddCommGroup U] {J N J' N' : Submodule ℤ U}
    (hb : J=J') (hz : N=N') : IntegralQuotient J N ≃ₗ[ℤ] IntegralQuotient J' N' := by
  subst J' N'
  exact LinearEquiv.refl _ _

private theorem reindex_mk {U : Type*} [AddCommGroup U] {J N J' N' : Submodule ℤ U}
    (hb : J=J') (hz : N=N') (z : N) :
    reindex hb hz ((identitiesInInvariant J N).mkQ z)=
      (identitiesInInvariant J' N').mkQ ⟨z.val,hz ▸ z.property⟩ := by
  subst J' N'
  rfl

def topPrimitiveEquiv (hp : PureInDimension K d) :
    TPrime (topFacetData (G:=G) K d n) ≃ₗ[ℤ] TPrime (facetRestrictionData (G:=G) K n) :=
  reindex (topPrimitiveSubmodules (G:=G) K d n hp).2 (topPrimitiveSubmodules (G:=G) K d n hp).1

theorem topPrimitiveEquiv_mk (hp : PureInDimension K d) (z : Zprim (topFacetData (G:=G) K d n)) :
    topPrimitiveEquiv K d n hp ((BprimInZprim _).mkQ z)=
      (BprimInZprim (facetRestrictionData (G:=G) K n)).mkQ
        ⟨z.val,(topPrimitiveSubmodules (G:=G) K d n hp).1 ▸ z.property⟩ :=
  reindex_mk _ _ z

end GeneralSphereT.Transport

