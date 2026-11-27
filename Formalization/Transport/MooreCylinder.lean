import Formalization.OpenDisk.PhaseDualityNativeChainHomotopy

/-! Reflect chain homotopies into a simplicial abelian cylinder. Only a
degreewise projection onto one end is used in the correction term. -/
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
noncomputable section
open CategoryTheory Opposite Simplicial AlgebraicTopology AlgebraicTopology.DoldKan
open HomologicalComplex CategoryTheory.Limits
namespace GeneralSphereT.Transport.RelativeChains
universe u
abbrev Moore := (CategoryTheory.Abelian.DoldKan.equivalence (A:=AddCommGrpCat.{u})).functor
variable {D E A : SimplicialObject AddCommGrpCat.{u}}

/-- Restrict a graded operation to Moore chains and project its output to Moore chains. -/
def moorePart (s : ∀ n : ℕ, E.obj (op ⦋n⦌) ⟶ D.obj (op ⦋n⦌)) (n : ℕ) :
    (Moore.obj E).X n ⟶ (Moore.obj D).X n :=
  (inclusionOfMooreComplexMap E).f n ≫ s n ≫ (PInftyToNormalizedMooreComplex D).f n

private theorem incl_nat (a : D ⟶ E) (n : ℕ) :
    (Moore.map a).f n ≫ (inclusionOfMooreComplexMap E).f n =
      (inclusionOfMooreComplexMap D).f n ≫ a.app (op ⦋n⦌) :=
  (HomologicalComplex.congr_hom ((inclusionOfMooreComplex AddCommGrpCat).naturality a) n)

private theorem moorePart_one (a : D ⟶ E) (s : ∀ n : ℕ, E.obj (op ⦋n⦌) ⟶ D.obj (op ⦋n⦌))
    (h : ∀ n, a.app (op ⦋n⦌) ≫ s n = 𝟙 _) (n : ℕ) :
    (Moore.map a).f n ≫ moorePart s n=𝟙 _ := by
  unfold moorePart
  rw [← Category.assoc, incl_nat, Category.assoc, ← Category.assoc (a.app _) _ _,h,Category.id_comp]
  exact HomologicalComplex.congr_hom (splitMonoInclusionOfMooreComplexMap D).id n

private theorem moorePart_zero (a : D ⟶ E) (s : ∀ n : ℕ, E.obj (op ⦋n⦌) ⟶ D.obj (op ⦋n⦌))
    (h : ∀ n, a.app (op ⦋n⦌) ≫ s n = 0) (n : ℕ) :
    (Moore.map a).f n ≫ moorePart s n=0 := by
  unfold moorePart
  rw [← Category.assoc,incl_nat,Category.assoc,← Category.assoc (a.app _) _ _,h,zero_comp,comp_zero]

/-- A chain homotopy yields a map from the given cylinder with the specified
two ends. There is no simplicial naturality requirement on the graded projection. -/
theorem extend_on_cylinder (a b : D ⟶ E) (p : E ⟶ D) (ha : a ≫ p=𝟙 _) (hb : b ≫ p=𝟙 _)
    (s : ∀ n : ℕ, E.obj (op ⦋n⦌) ⟶ D.obj (op ⦋n⦌))
    (h₀ : ∀ n, a.app (op ⦋n⦌) ≫ s n=𝟙 _) (h₁ : ∀ n, b.app (op ⦋n⦌) ≫ s n=0)
    {f g : D ⟶ A} (H : _root_.Homotopy (Moore.map f) (Moore.map g)) :
    ∃ k : E ⟶ A, a ≫ k=f ∧ b ≫ k=g := by
  let t := fun i j => moorePart s i ≫ H.hom i j
  let k := (Moore.map p ≫ Moore.map g) + Homotopy.nullHomotopicMap t
  have atEnd (e : D ⟶ E) (he : e ≫ p=𝟙 _) : Moore.map e ≫ (Moore.map p ≫ Moore.map g) = Moore.map g := by
    rw [← Category.assoc,← Functor.map_comp,he,Moore.map_id,Category.id_comp]
  have ea : Moore.map a ≫ Homotopy.nullHomotopicMap t = Homotopy.nullHomotopicMap H.hom := by
    rw [Homotopy.comp_nullHomotopicMap]
    apply congrArg Homotopy.nullHomotopicMap
    funext i j
    change _ ≫ moorePart s i ≫ H.hom i j = H.hom i j
    rw [← Category.assoc,moorePart_one a s h₀,Category.id_comp]
  have eb : Moore.map b ≫ Homotopy.nullHomotopicMap t = 0 := by
    rw [Homotopy.comp_nullHomotopicMap]
    have eq : (fun i j => (Moore.map b).f i ≫ t i j) = (fun i j => (0 : (Moore.obj D).X i ⟶ (Moore.obj A).X j)) := by
      funext i j
      change _ ≫ moorePart s i ≫ H.hom i j = _
      rw [← Category.assoc,moorePart_zero b s h₁,zero_comp]
    rw [eq]
    ext n
    simp [Homotopy.nullHomotopicMap,dNext,prevD]
  refine ⟨Moore.preimage k,Moore.map_injective ?_,Moore.map_injective ?_⟩
  · rw [Functor.map_comp,Functor.map_preimage]
    change Moore.map a ≫ ((Moore.map p ≫ Moore.map g) + _) = Moore.map f
    rw [Preadditive.comp_add,atEnd a ha,ea]
    ext1 n
    change (Moore.map g).f n + (dNext n H.hom + prevD n H.hom)=(Moore.map f).f n
    rw [add_comm]
    exact (H.comm n).symm
  · rw [Functor.map_comp,Functor.map_preimage]
    change Moore.map b ≫ ((Moore.map p ≫ Moore.map g) + _) = Moore.map g
    rw [Preadditive.comp_add,atEnd b hb,eb,add_zero]

end GeneralSphereT.Transport.RelativeChains
