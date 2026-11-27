import Formalization.PrimitiveQuotientFunctoriality
import Formalization.Section4ReducedFreeFiber
import Formalization.Section4NormalizedPathFibers

set_option linter.style.header false
set_option backward.isDefEq.respectTransparency false

/-!
# Section 4: the simplicial path object and its boundary

The path quotient used throughout the paper is functorial in both the
increment and base variables.  Applied degreewise to simplicial abelian
groups, it is therefore itself a simplicial abelian group.  The primitive
boundary is a genuine natural transformation to the reduced free abelian
group.  This is the tensor-free version of the map `μ` in (4.21).
-/

noncomputable section

open CategoryTheory CategoryTheory.Category

namespace GeneralSphereT.StandardModels

open GeneralSphereT.PathAlgebra

universe u

variable {I I' X X' : Type u}
variable [AddCommGroup I] [AddCommGroup I']
variable [AddCommGroup X] [AddCommGroup X']

/-- Raw base augmentation is natural in the increment label. -/
theorem rawBaseAug_rawMapPath
    (i : I →+ I') (b : X →+ X') :
    (rawBaseAug (I := I') (X := X')).comp (rawMapPath i b) =
      (mapRedDist i).comp (rawBaseAug (I := I) (X := X)) := by
  ext a
  rcases a with ⟨r, x⟩
  simp [rawBaseAug, rawMapPath]

/-- Base augmentation is natural when both path labels are mapped. -/
theorem baseAug_mapPath
    (i : I →+ I') (b : X →+ X') (p : Path I X) :
    baseAug (I := I') (X := X') (mapPath i b p) =
      mapRedDist i (baseAug (I := I) (X := X) p) := by
  refine Submodule.Quotient.induction_on
    (p := zeroIncrement I X) p ?_
  intro z
  change rawBaseAug (I := I') (X := X') (rawMapPath i b z) =
    mapRedDist i (rawBaseAug (I := I) (X := X) z)
  exact LinearMap.congr_fun (rawBaseAug_rawMapPath i b) z

/-- Mapping both labels by identity acts trivially on path classes. -/
@[simp]
theorem mapPath_id_id_apply (p : Path I X) :
    mapPath (AddMonoidHom.id I) (AddMonoidHom.id X) p = p := by
  exact mapPath_id_apply p

/-- If every increment is sent to zero, the path quotient vanishes. -/
@[simp]
theorem mapPath_zero_left (b : X →+ X') (p : Path I X) :
    mapPath (0 : I →+ I') b p = 0 := by
  refine Submodule.Quotient.induction_on
    (p := zeroIncrement I X) p ?_
  intro z
  induction z using Finsupp.induction with
  | zero => simp
  | single_add a n z ha hn ih =>
      rcases a with ⟨r, x⟩
      rw [Submodule.Quotient.mk_add, map_add, ih, add_zero]
      unfold mapPath
      rw [Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero]
      change rawMapPath (0 : I →+ I') b
        (Finsupp.single (r, x) n) ∈ zeroIncrement I' X'
      rw [show rawMapPath (0 : I →+ I') b
          (Finsupp.single (r, x) n) = Finsupp.single (0, b x) n by
        simp [rawMapPath]]
      change Finsupp.single (0, b x) n ∈ zeroIncrement I' X'
      rw [show Finsupp.single (0, b x) n =
          n • rawEdge (0 : I') (b x) by
        simp [rawEdge]]
      exact Submodule.smul_mem _ n
        (Submodule.subset_span (Set.mem_range_self (b x)))

/-- The path quotient as a functor of its increment and base groups. -/
def pathBaseFunctor :
    AddCommGrpCat.{u} × AddCommGrpCat.{u} ⥤ AddCommGrpCat.{u} where
  obj P := AddCommGrpCat.of (Path P.1 P.2)
  map f := AddCommGrpCat.ofHom
    (mapPath f.1.hom f.2.hom).toAddMonoidHom
  map_id P := by
    apply AddCommGrpCat.ext
    intro p
    exact mapPath_id_id_apply p
  map_comp f g := by
    apply AddCommGrpCat.ext
    intro p
    exact (mapPath_comp_apply
      f.1.hom f.2.hom g.1.hom g.2.hom p).symm

/-- Apply the paper's path quotient degreewise to two simplicial abelian
groups. -/
def simplicialPath
    (A B : SimplicialObject AddCommGrpCat.{u}) :
    SimplicialObject AddCommGrpCat.{u} :=
  A.prod' B ⋙ pathBaseFunctor

@[simp]
theorem simplicialPath_map_apply
    (A B : SimplicialObject AddCommGrpCat.{u})
    {Δ Δ' : SimplexCategoryᵒᵖ} (θ : Δ ⟶ Δ')
    (p : Path (A.obj Δ) (B.obj Δ)) :
    (simplicialPath A B).map θ p =
      mapPath (A.map θ).hom (B.map θ).hom p :=
  rfl

/-- Base augmentation as a simplicial natural transformation. -/
def simplicialBaseAug
    (A B : SimplicialObject AddCommGrpCat.{u}) :
    simplicialPath A B ⟶ reducedFree A where
  app Δ := AddCommGrpCat.ofHom
    (baseAug (I := A.obj Δ) (X := B.obj Δ)).toAddMonoidHom
  naturality Δ Δ' θ := by
    apply AddCommGrpCat.ext
    intro p
    change baseAug
        (mapPath (A.map θ).hom (B.map θ).hom p) =
      mapRedDist (A.map θ).hom (baseAug p)
    exact baseAug_mapPath (A.map θ).hom (B.map θ).hom p

/-- Primitive path boundary as a genuine simplicial homomorphism. -/
def simplicialPrimitiveBoundary
    (A : SimplicialObject AddCommGrpCat.{u}) :
    simplicialPath A A ⟶ reducedFree A where
  app Δ := AddCommGrpCat.ofHom
    (primitiveReducedBoundary (A.obj Δ)).toAddMonoidHom
  naturality Δ Δ' θ := by
    apply AddCommGrpCat.ext
    intro p
    change primitiveReducedBoundary (A.obj Δ')
        (mapPath (A.map θ).hom (A.map θ).hom p) =
      mapRedDist (A.map θ).hom
        (primitiveReducedBoundary (A.obj Δ) p)
    exact (LinearMap.congr_fun
      (reducedBoundary_natural
        (AddMonoidHom.id (A.obj Δ))
        (AddMonoidHom.id (A.obj Δ'))
        (A.map θ).hom (A.map θ).hom rfl) p).symm

@[simp]
theorem simplicialPrimitiveBoundary_app_apply
    (A : SimplicialObject AddCommGrpCat.{u})
    (Δ : SimplexCategoryᵒᵖ) (p : Path (A.obj Δ) (A.obj Δ)) :
    (simplicialPrimitiveBoundary A).app Δ p =
      primitiveReducedBoundary (A.obj Δ) p :=
  rfl

/-! ## Normalized and relation-path subobjects -/

/-- Functoriality of the base-normalized path subgroup. -/
def mapNormalizedPath
    (i : I →+ I') (b : X →+ X') :
    NormalizedPath I X →ₗ[ℤ] NormalizedPath I' X' :=
  LinearMap.codRestrict (NormalizedPath I' X')
    ((mapPath i b).comp (NormalizedPath I X).subtype) fun p => by
      rw [LinearMap.mem_ker]
      change baseAug (mapPath i b p.1) = 0
      rw [baseAug_mapPath]
      rw [p.2, map_zero]

@[simp]
theorem mapNormalizedPath_coe
    (i : I →+ I') (b : X →+ X') (p : NormalizedPath I X) :
    (mapNormalizedPath i b p : Path I' X') = mapPath i b p.1 :=
  rfl

@[simp]
theorem mapNormalizedPath_id_apply (p : NormalizedPath I X) :
    mapNormalizedPath (AddMonoidHom.id I) (AddMonoidHom.id X) p = p := by
  apply Subtype.ext
  exact mapPath_id_apply p.1

theorem mapNormalizedPath_comp_apply
    {I'' X'' : Type u} [AddCommGroup I''] [AddCommGroup X'']
    (i : I →+ I') (b : X →+ X')
    (i' : I' →+ I'') (b' : X' →+ X'')
    (p : NormalizedPath I X) :
    mapNormalizedPath i' b' (mapNormalizedPath i b p) =
      mapNormalizedPath (i'.comp i) (b'.comp b) p := by
  apply Subtype.ext
  exact mapPath_comp_apply i b i' b' p.1

/-- Applying a map to both labels commutes with applying a differential to
the base label, provided the evident square commutes.  The increment map is
independent of that square. -/
theorem mapDNormalizedPath_mapNormalizedPath
    {C C' B B' : Type u}
    [AddCommGroup C] [AddCommGroup C']
    [AddCommGroup B] [AddCommGroup B']
    (d : C →+ B) (d' : C' →+ B')
    (i a : C →+ C') (b : B →+ B')
    (h : d'.comp a = b.comp d)
    (p : NormalizedPath C C) :
    mapDNormalizedPath d' (mapNormalizedPath i a p) =
      mapNormalizedPath i b (mapDNormalizedPath d p) := by
  apply Subtype.ext
  change mapPath (AddMonoidHom.id C') d'
      (mapPath i a p.1) =
    mapPath i b (mapPath (AddMonoidHom.id C) d p.1)
  calc
    _ = mapPath i (d'.comp a) p.1 := by
      simpa using mapPath_comp_apply i a
        (AddMonoidHom.id C') d' p.1
    _ = mapPath i (b.comp d) p.1 := by rw [h]
    _ = _ := by
      simpa using (mapPath_comp_apply
        (AddMonoidHom.id C) d i b p.1).symm

/-- Pointwise version of `mapDNormalizedPath_mapNormalizedPath`.  This is
useful when the commuting square is assembled from large bundled maps (for
example Dold--Kan evaluation maps), since it avoids asking elaboration to
normalize the two composites before the mathematical proof begins. -/
theorem mapDNormalizedPath_mapNormalizedPath_of_apply
    {C C' B B' : Type u}
    [AddCommGroup C] [AddCommGroup C']
    [AddCommGroup B] [AddCommGroup B']
    (d : C →+ B) (d' : C' →+ B')
    (i a : C →+ C') (b : B →+ B')
    (h : ∀ c, d' (a c) = b (d c))
    (p : NormalizedPath C C) :
    mapDNormalizedPath d' (mapNormalizedPath i a p) =
      mapNormalizedPath i b (mapDNormalizedPath d p) := by
  apply mapDNormalizedPath_mapNormalizedPath d d' i a b
  apply AddMonoidHom.ext
  exact h

/-- Base-normalized paths as a functor of two abelian groups. -/
def normalizedPathBaseFunctor :
    AddCommGrpCat.{u} × AddCommGrpCat.{u} ⥤ AddCommGrpCat.{u} where
  obj P := AddCommGrpCat.of (NormalizedPath P.1 P.2)
  map f := AddCommGrpCat.ofHom
    (mapNormalizedPath f.1.hom f.2.hom).toAddMonoidHom
  map_id P := by
    apply AddCommGrpCat.ext
    intro p
    exact mapNormalizedPath_id_apply p
  map_comp f g := by
    apply AddCommGrpCat.ext
    intro p
    exact (mapNormalizedPath_comp_apply
      f.1.hom f.2.hom g.1.hom g.2.hom p).symm

/-- The degreewise normalized path groups form a simplicial abelian group. -/
def simplicialNormalizedPath
    (A B : SimplicialObject AddCommGrpCat.{u}) :
    SimplicialObject AddCommGrpCat.{u} :=
  A.prod' B ⋙ normalizedPathBaseFunctor

/-- Forget normalization, degreewise and naturally. -/
def normalizedPathInclusion
    (A B : SimplicialObject AddCommGrpCat.{u}) :
    simplicialNormalizedPath A B ⟶ simplicialPath A B where
  app Δ := AddCommGrpCat.ofHom
    (NormalizedPath (A.obj Δ) (B.obj Δ)).subtype.toAddMonoidHom
  naturality Δ Δ' θ := by
    apply AddCommGrpCat.ext
    intro p
    rfl

/-- Applying a simplicial homomorphism to the base label of a normalized
path. -/
def simplicialMapDNormalized
    {A B : SimplicialObject AddCommGrpCat.{u}} (d : A ⟶ B) :
    simplicialNormalizedPath A A ⟶ simplicialNormalizedPath A B where
  app Δ := AddCommGrpCat.ofHom
    (mapDNormalizedPath (d.app Δ).hom).toAddMonoidHom
  naturality Δ Δ' θ := by
    apply AddCommGrpCat.ext
    intro p
    apply Subtype.ext
    change mapPath (AddMonoidHom.id (A.obj Δ')) (d.app Δ').hom
        (mapPath (A.map θ).hom (A.map θ).hom p.1) =
      mapPath (A.map θ).hom (B.map θ).hom
        (mapPath (AddMonoidHom.id (A.obj Δ)) (d.app Δ).hom p.1)
    calc
      _ = mapPath (A.map θ).hom
          ((d.app Δ').hom.comp (A.map θ).hom) p.1 := by
        simpa using mapPath_comp_apply
          (A.map θ).hom (A.map θ).hom
          (AddMonoidHom.id (A.obj Δ')) (d.app Δ').hom p.1
      _ = mapPath (A.map θ).hom
          ((B.map θ).hom.comp (d.app Δ).hom) p.1 := by
        have h : (d.app Δ').hom.comp (A.map θ).hom =
            (B.map θ).hom.comp (d.app Δ).hom :=
          congrArg (fun f => f.hom) (d.naturality θ)
        exact congrArg (fun e => mapPath (A.map θ).hom e p.1) h
      _ = _ := by
        simpa using (mapPath_comp_apply
          (AddMonoidHom.id (A.obj Δ)) (d.app Δ).hom
          (A.map θ).hom (B.map θ).hom p.1).symm

/-- The tensor-free relation-path object: normalized paths killed after
applying `d` to their base label. -/
def simplicialRelationPath
    {A B : SimplicialObject AddCommGrpCat.{u}} (d : A ⟶ B) :
    SimplicialObject AddCommGrpCat.{u} where
  obj Δ := AddCommGrpCat.of
    (LinearMap.ker (mapDNormalizedPath (d.app Δ).hom))
  map {Δ Δ'} θ := AddCommGrpCat.ofHom
    (LinearMap.codRestrict
      (LinearMap.ker (mapDNormalizedPath (d.app Δ').hom))
      ((mapNormalizedPath (A.map θ).hom (A.map θ).hom).comp
        (LinearMap.ker (mapDNormalizedPath (d.app Δ).hom)).subtype)
      (fun p => by
        rw [LinearMap.mem_ker]
        have hnat := ConcreteCategory.congr_hom
          ((simplicialMapDNormalized d).naturality θ) p.1
        calc
          _ = mapNormalizedPath (A.map θ).hom (B.map θ).hom
              (mapDNormalizedPath (d.app Δ).hom p.1) := hnat
          _ = 0 := by rw [p.2, map_zero])).toAddMonoidHom
  map_id Δ := by
    apply AddCommGrpCat.ext
    intro p
    apply Subtype.ext
    change mapNormalizedPath (A.map (𝟙 Δ)).hom
        (A.map (𝟙 Δ)).hom p.1 = p.1
    have hA : (A.map (𝟙 Δ)).hom = AddMonoidHom.id (A.obj Δ) :=
      congrArg (fun f => f.hom) (A.map_id Δ)
    rw [hA]
    exact mapNormalizedPath_id_apply p.1
  map_comp θ φ := by
    apply AddCommGrpCat.ext
    intro p
    apply Subtype.ext
    change mapNormalizedPath (A.map (θ ≫ φ)).hom
        (A.map (θ ≫ φ)).hom p.1 =
      mapNormalizedPath (A.map φ).hom (A.map φ).hom
        (mapNormalizedPath (A.map θ).hom (A.map θ).hom p.1)
    have hA : (A.map (θ ≫ φ)).hom =
        (A.map φ).hom.comp (A.map θ).hom :=
      congrArg (fun f => f.hom) (A.map_comp θ φ)
    rw [hA]
    exact (mapNormalizedPath_comp_apply
      (A.map θ).hom (A.map θ).hom
      (A.map φ).hom (A.map φ).hom p.1).symm

/-- Inclusion of relation paths into normalized paths. -/
def relationPathInclusion
    {A B : SimplicialObject AddCommGrpCat.{u}} (d : A ⟶ B) :
    simplicialRelationPath d ⟶ simplicialNormalizedPath A A where
  app Δ := AddCommGrpCat.ofHom
    (LinearMap.ker (mapDNormalizedPath (d.app Δ).hom)).subtype.toAddMonoidHom
  naturality Δ Δ' θ := by
    apply AddCommGrpCat.ext
    intro p
    apply Subtype.ext
    rfl

/-- The boundary map `μ` of (4.21), defined on the actual simplicial object
of normalized relation paths. -/
def simplicialRelationBoundary
    {A B : SimplicialObject AddCommGrpCat.{u}} (d : A ⟶ B) :
    simplicialRelationPath d ⟶ reducedFree A :=
  relationPathInclusion d ≫ normalizedPathInclusion A A ≫
    simplicialPrimitiveBoundary A

@[simp]
theorem simplicialRelationBoundary_app_apply
    {A B : SimplicialObject AddCommGrpCat.{u}} (d : A ⟶ B)
    (Δ : SimplexCategoryᵒᵖ)
    (R : LinearMap.ker (mapDNormalizedPath (d.app Δ).hom)) :
    (simplicialRelationBoundary d).app Δ R =
      primitiveReducedBoundary (A.obj Δ) R.1.1 :=
  rfl

end GeneralSphereT.StandardModels
