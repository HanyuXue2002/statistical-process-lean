import Formalization.Section4SimplicialPathObject
import Formalization.Section4ReducedFreeContractibility
import Formalization.Section4DoldKanDiskExtraDegeneracy

set_option linter.style.header false
set_option backward.isDefEq.respectTransparency false

/-!
# Section 4: contraction of the relation-path object

The first label of a normalized relation path lies in the contractible
Dold--Kan disk `L`, while the base label is held fixed.  This file implements
the tensor-free form of that contraction.  Composing it with the natural
boundary map constructed in `Section4SimplicialPathObject` is the formal
content of the contraction paragraph (4.21).
-/

noncomputable section

open CategoryTheory CategoryTheory.Category Opposite Simplicial
open CategoryTheory.Prod

namespace GeneralSphereT.StandardModels

open GeneralSphereT.PathAlgebra
open DoldKanDiskContraction

universe u

/-! ## Homotopies in two variables -/

/-- Pair two combinatorial simplicial homotopies with the same source
simplex category. -/
def homotopyProd'
    {A A' B B' : SimplicialObject AddCommGrpCat.{u}}
    {fA gA : A ⟶ A'} {fB gB : B ⟶ B'}
    (H : SimplicialObject.Homotopy fA gA)
    (K : SimplicialObject.Homotopy fB gB) :
    SimplicialObject.Homotopy
      (NatTrans.prod' fA fB) (NatTrans.prod' gA gB) where
  h i := H.h i ×ₘ K.h i
  h_zero_comp_δ_zero n := by
    apply CategoryTheory.Prod.hom_ext
    · exact H.h_zero_comp_δ_zero n
    · exact K.h_zero_comp_δ_zero n
  h_last_comp_δ_last n := by
    apply CategoryTheory.Prod.hom_ext
    · exact H.h_last_comp_δ_last n
    · exact K.h_last_comp_δ_last n
  h_succ_comp_δ_castSucc_of_lt i j hij := by
    apply CategoryTheory.Prod.hom_ext
    · exact H.h_succ_comp_δ_castSucc_of_lt i j hij
    · exact K.h_succ_comp_δ_castSucc_of_lt i j hij
  h_succ_comp_δ_castSucc_succ j := by
    apply CategoryTheory.Prod.hom_ext
    · exact H.h_succ_comp_δ_castSucc_succ j
    · exact K.h_succ_comp_δ_castSucc_succ j
  h_castSucc_comp_δ_succ_of_lt i j hji := by
    apply CategoryTheory.Prod.hom_ext
    · exact H.h_castSucc_comp_δ_succ_of_lt i j hji
    · exact K.h_castSucc_comp_δ_succ_of_lt i j hji
  h_comp_σ_castSucc_of_le i j hij := by
    apply CategoryTheory.Prod.hom_ext
    · exact H.h_comp_σ_castSucc_of_le i j hij
    · exact K.h_comp_σ_castSucc_of_le i j hij
  h_comp_σ_succ_of_lt i j hji := by
    apply CategoryTheory.Prod.hom_ext
    · exact H.h_comp_σ_succ_of_lt i j hji
    · exact K.h_comp_σ_succ_of_lt i j hji

/-- A pair of homotopies induces a homotopy on normalized path objects. -/
def normalizedPathHomotopy
    {A A' B B' : SimplicialObject AddCommGrpCat.{u}}
    {fA gA : A ⟶ A'} {fB gB : B ⟶ B'}
    (H : SimplicialObject.Homotopy fA gA)
    (K : SimplicialObject.Homotopy fB gB) :
    SimplicialObject.Homotopy
      (((SimplicialObject.whiskering
          (AddCommGrpCat.{u} × AddCommGrpCat.{u}) AddCommGrpCat.{u}).obj
        normalizedPathBaseFunctor).map (NatTrans.prod' fA fB))
      (((SimplicialObject.whiskering
          (AddCommGrpCat.{u} × AddCommGrpCat.{u}) AddCommGrpCat.{u}).obj
        normalizedPathBaseFunctor).map (NatTrans.prod' gA gB)) :=
  (homotopyProd' H K).whiskerRight normalizedPathBaseFunctor

/-- Mapping all increment labels to zero annihilates normalized paths. -/
theorem normalizedPathBaseFunctor_map_zero_left
    (A B : SimplicialObject AddCommGrpCat.{u}) :
    ((SimplicialObject.whiskering
        (AddCommGrpCat.{u} × AddCommGrpCat.{u}) AddCommGrpCat.{u}).obj
      normalizedPathBaseFunctor).map
        (NatTrans.prod' (0 : A ⟶ A) (𝟙 B)) = 0 := by
  ext Δ p
  apply Subtype.ext
  exact mapPath_zero_left (AddMonoidHom.id (B.obj Δ)) p.1

/-- Mapping both labels by the identity is the identity of the normalized
path object. -/
theorem normalizedPathBaseFunctor_map_id_id
    (A B : SimplicialObject AddCommGrpCat.{u}) :
    ((SimplicialObject.whiskering
        (AddCommGrpCat.{u} × AddCommGrpCat.{u}) AddCommGrpCat.{u}).obj
      normalizedPathBaseFunctor).map
        (NatTrans.prod' (𝟙 A) (𝟙 B)) =
      𝟙 (simplicialNormalizedPath A B) := by
  ext Δ p
  apply Subtype.ext
  exact mapPath_id_apply p.1

/-- The unreduced-endpoint form of first-factor contraction.  Its prism
operators are definitionally the maps on labels used below. -/
def normalizedPathFirstFactorRawHomotopy
    {A : SimplicialObject AddCommGrpCat.{u}}
    (H : SimplicialContraction A) :
    SimplicialObject.Homotopy
      (((SimplicialObject.whiskering
          (AddCommGrpCat.{u} × AddCommGrpCat.{u}) AddCommGrpCat.{u}).obj
        normalizedPathBaseFunctor).map
          (NatTrans.prod' (0 : A ⟶ A) (𝟙 A)))
      (((SimplicialObject.whiskering
          (AddCommGrpCat.{u} × AddCommGrpCat.{u}) AddCommGrpCat.{u}).obj
        normalizedPathBaseFunctor).map
          (NatTrans.prod' (𝟙 A) (𝟙 A))) :=
  normalizedPathHomotopy H (SimplicialObject.Homotopy.refl (𝟙 A))

/-- Contract the increment label of normalized paths while holding the base
label fixed. -/
def normalizedPathFirstFactorContraction
    {A : SimplicialObject AddCommGrpCat.{u}}
    (H : SimplicialContraction A) :
    SimplicialContraction (simplicialNormalizedPath A A) := by
  let K := SimplicialObject.Homotopy.refl (𝟙 A)
  let H' := normalizedPathHomotopy H K
  rw [normalizedPathBaseFunctor_map_zero_left A A,
    normalizedPathBaseFunctor_map_id_id A A] at H'
  exact H'

@[simp]
theorem normalizedPathFirstFactorRawHomotopy_h_apply
    {A : SimplicialObject AddCommGrpCat.{u}}
    (H : SimplicialContraction A) {n : ℕ} (i : Fin (n + 1))
    (p : NormalizedPath (A.obj (op ⦋n⦌)) (A.obj (op ⦋n⦌))) :
    ((normalizedPathFirstFactorRawHomotopy H).h i).hom p =
      mapNormalizedPath (H.h i).hom (A.σ i).hom p :=
  rfl

/-! ## The relation-path contraction -/

/-- The prism operator on normalized paths preserves the kernel defining
relation paths. -/
theorem normalizedPathContraction_mem_relation
    {A B : SimplicialObject AddCommGrpCat.{u}} (d : A ⟶ B)
    (H : SimplicialContraction A) {n : ℕ} (i : Fin (n + 1))
    (R : LinearMap.ker
      (mapDNormalizedPath (d.app (op ⦋n⦌)).hom)) :
    mapNormalizedPath (H.h i).hom (A.σ i).hom R.1 ∈
      LinearMap.ker
        (mapDNormalizedPath (d.app (op ⦋n + 1⦌)).hom) := by
  rw [LinearMap.mem_ker]
  have hd : (d.app (op ⦋n + 1⦌)).hom.comp (A.σ i).hom =
      (B.σ i).hom.comp (d.app (op ⦋n⦌)).hom :=
    congrArg (fun f => f.hom) (SimplicialObject.σ_naturality d i)
  calc
    mapDNormalizedPath (d.app (op ⦋n + 1⦌)).hom
        (mapNormalizedPath (H.h i).hom (A.σ i).hom R.1) =
      mapNormalizedPath (H.h i).hom (B.σ i).hom
        (mapDNormalizedPath (d.app (op ⦋n⦌)).hom R.1) :=
      mapDNormalizedPath_mapNormalizedPath
        (d.app (op ⦋n⦌)).hom
        (d.app (op ⦋n + 1⦌)).hom
        (H.h i).hom (A.σ i).hom (B.σ i).hom hd R.1
    _ = 0 := by rw [R.2, map_zero]

/-- Contract the first label of the actual simplicial relation-path object.
The second label is carried by the constant homotopy, so the `d`-kernel is
preserved in every prism degree. -/
def relationPathFirstFactorContraction
    {A B : SimplicialObject AddCommGrpCat.{u}} (d : A ⟶ B)
    (H : SimplicialContraction A) :
    SimplicialContraction (simplicialRelationPath d) where
  h {n} i := AddCommGrpCat.ofHom
    (LinearMap.codRestrict
      (LinearMap.ker
        (mapDNormalizedPath (d.app (op ⦋n + 1⦌)).hom))
      ((mapNormalizedPath (H.h i).hom (A.σ i).hom).comp
        (LinearMap.ker
          (mapDNormalizedPath (d.app (op ⦋n⦌)).hom)).subtype)
      (normalizedPathContraction_mem_relation d H i)).toAddMonoidHom
  h_zero_comp_δ_zero n := by
    apply AddCommGrpCat.ext
    intro R
    apply Subtype.ext
    calc
      _ = (((SimplicialObject.whiskering
            (AddCommGrpCat.{u} × AddCommGrpCat.{u}) AddCommGrpCat.{u}).obj
          normalizedPathBaseFunctor).map
            (NatTrans.prod' (𝟙 A) (𝟙 A))).app (op ⦋n⦌) R.1 :=
        ConcreteCategory.congr_hom
          ((normalizedPathFirstFactorRawHomotopy H).h_zero_comp_δ_zero n) R.1
      _ = R.1 := by
        rw [normalizedPathBaseFunctor_map_id_id A A]
        rfl
  h_last_comp_δ_last n := by
    apply AddCommGrpCat.ext
    intro R
    apply Subtype.ext
    calc
      _ = (((SimplicialObject.whiskering
            (AddCommGrpCat.{u} × AddCommGrpCat.{u}) AddCommGrpCat.{u}).obj
          normalizedPathBaseFunctor).map
            (NatTrans.prod' (0 : A ⟶ A) (𝟙 A))).app (op ⦋n⦌) R.1 :=
        ConcreteCategory.congr_hom
          ((normalizedPathFirstFactorRawHomotopy H).h_last_comp_δ_last n) R.1
      _ = 0 := by
        rw [normalizedPathBaseFunctor_map_zero_left A A]
        rfl
  h_succ_comp_δ_castSucc_of_lt i j hij := by
    apply AddCommGrpCat.ext
    intro R
    apply Subtype.ext
    exact ConcreteCategory.congr_hom
      ((normalizedPathFirstFactorRawHomotopy H).h_succ_comp_δ_castSucc_of_lt i j hij) R.1
  h_succ_comp_δ_castSucc_succ j := by
    apply AddCommGrpCat.ext
    intro R
    apply Subtype.ext
    exact ConcreteCategory.congr_hom
      ((normalizedPathFirstFactorRawHomotopy H).h_succ_comp_δ_castSucc_succ j) R.1
  h_castSucc_comp_δ_succ_of_lt i j hji := by
    apply AddCommGrpCat.ext
    intro R
    apply Subtype.ext
    exact ConcreteCategory.congr_hom
      ((normalizedPathFirstFactorRawHomotopy H).h_castSucc_comp_δ_succ_of_lt i j hji) R.1
  h_comp_σ_castSucc_of_le i j hij := by
    apply AddCommGrpCat.ext
    intro R
    apply Subtype.ext
    exact ConcreteCategory.congr_hom
      ((normalizedPathFirstFactorRawHomotopy H).h_comp_σ_castSucc_of_le i j hij) R.1
  h_comp_σ_succ_of_lt i j hji := by
    apply AddCommGrpCat.ext
    intro R
    apply Subtype.ext
    exact ConcreteCategory.congr_hom
      ((normalizedPathFirstFactorRawHomotopy H).h_comp_σ_succ_of_lt i j hji) R.1

/-- The relation boundary itself is simplicially homotopic to zero. -/
def relationBoundaryContraction
    {A B : SimplicialObject AddCommGrpCat.{u}} (d : A ⟶ B)
    (H : SimplicialContraction A) :
    SimplicialObject.Homotopy
      (0 : simplicialRelationPath d ⟶ reducedFree A)
      (simplicialRelationBoundary d) := by
  let H' := (relationPathFirstFactorContraction d H).postcomp
    (simplicialRelationBoundary d)
  simpa using H'

/-- Specialization to the standard Dold--Kan disk. -/
def standardRelationPathContraction
    (G : AddCommGrpCat.{u}) (q : ℕ) :
    SimplicialContraction
      (simplicialRelationPath (d G (q + 1))) :=
  relationPathFirstFactorContraction (d G (q + 1))
    (standardDiskSimplicialContraction G q)

/-- Specialization of (4.21): the standard relation boundary is genuinely
nullhomotopic as a simplicial homomorphism. -/
def standardRelationBoundaryContraction
    (G : AddCommGrpCat.{u}) (q : ℕ) :
    SimplicialObject.Homotopy
      (0 : simplicialRelationPath (d G (q + 1)) ⟶
        reducedFree (L G (q + 1)))
      (simplicialRelationBoundary (d G (q + 1))) :=
  relationBoundaryContraction (d G (q + 1))
    (standardDiskSimplicialContraction G q)

end GeneralSphereT.StandardModels
