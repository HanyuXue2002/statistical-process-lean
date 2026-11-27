import Formalization.OpenDisk.StarLocality
import Formalization.Section4DoubleConeCohomologyShift
import Formalization.Section3ApexFreeCoboundary

/-!
# Literal cone cochains and their new/boundary coordinates

The new coordinates are extracted by the signed simplicial cone homotopy.
Consequently the coordinate formula respects the actual ordered coboundary,
rather than assuming a block matrix for it. The resulting inverse is
`(u,b) ↦ d (extend u) + extend (b - d u)`.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000

namespace OpenDisk.ConePhaseLiteralCoordinates

open GeneralSphereT.SimplicialCochain

variable {V W G : Type*} [LinearOrder V] [LinearOrder W] [Fintype V] [Fintype W]
  [AddCommGroup G]
variable {K : AbstractSimplicialComplex V} {L : AbstractSimplicialComplex W}

/-- The actual zero extension is additive; its simplex choice depends only
on the embedding, never on the coefficient table. -/
def zeroExtensionHom (F : OrderedSimplicialMap K L) (n : ℕ) :
    Cochain K n G →+ Cochain L n G where
  toFun := F.extendCochainByZero n
  map_zero' := F.extendCochainByZero_zero n
  map_add' c c' := by
    classical
    ext τ
    simp only [OrderedSimplicialMap.extendCochainByZero,
      Finsupp.equivFunOnFinite_symm_apply_apply]
    split_ifs <;> simp

theorem zeroExtensionHom_pullback (F : OrderedSimplicialMap K L) (n : ℕ)
    (c : Cochain K n G) :
    F.pullback n (zeroExtensionHom F n c) = c :=
  F.pullback_extendCochainByZero n c

variable (K : AbstractSimplicialComplex V)

local instance coneOrder : LinearOrder (Option V) := @WithBot.linearOrder V inferInstance

def bottomRestriction (n : ℕ) : Cochain (simplicialCone K) n G →+ Cochain K n G :=
  (coneBottomInclusion K).pullbackAddHom n

def bottomExtension (n : ℕ) : Cochain K n G →+ Cochain (simplicialCone K) n G :=
  zeroExtensionHom (coneBottomInclusion K) n

@[simp] theorem restriction_extension (n : ℕ) (c : Cochain K n G) :
    bottomRestriction K n (bottomExtension K n c) = c :=
  zeroExtensionHom_pullback (coneBottomInclusion K) n c

theorem restriction_coboundary (n : ℕ) (c : Cochain (simplicialCone K) n G) :
    bottomRestriction K (n + 1) (coboundary (simplicialCone K) n c) =
      coboundary K n (bottomRestriction K n c) := by
  ext σ
  exact (coneBottomInclusion K).pullback_coboundary_apply n c σ

theorem extension_apex_zero (n : ℕ) (c : Cochain K n G)
    (τ : Simplex (simplicialCone K) n) (hτ : none ∈ τ.val) :
    bottomExtension K n c τ = 0 := by
  classical
  change (coneBottomInclusion K).extendCochainByZero n c τ = 0
  simp only [OrderedSimplicialMap.extendCochainByZero,
    Finsupp.equivFunOnFinite_symm_apply_apply]
  split_ifs with h
  · obtain ⟨σ, hσ⟩ := h
    have hn : (none : Option V) ∉ ((coneBottomInclusion K).mapSimplex σ).val := by
      simp [OrderedSimplicialMap.mapSimplex, coneBottomInclusion,
        coneBottomOrderEmbedding]
    exact (hn (hσ ▸ hτ)).elim
  · rfl

theorem extension_restriction_of_apex_zero (n : ℕ)
    (c : Cochain (simplicialCone K) n G)
    (hc : ∀ τ, none ∈ τ.val → c τ = 0) :
    bottomExtension K n (bottomRestriction K n c) = c := by
  ext τ
  by_cases hτ : none ∈ τ.val
  · rw [extension_apex_zero K n _ τ hτ, hc τ hτ]
  · obtain ⟨σ, rfl⟩ := exists_coneBottom_simplex_of_apex_not_mem K n τ hτ
    exact (coneBottomInclusion K).extendCochainByZero_apply_of_eq n _ σ

def coneHomotopyGlobal (n : ℕ) :
    Cochain (simplicialCone K) (n + 1) G →+ Cochain (simplicialCone K) n G :=
  StarLocality.starPrimitiveExtension (simplicialCone K)
    (coneApexSimplex (simplicialCone K) none) none
    (mem_coneApexSimplex (simplicialCone K) none) n

local notation "L" => simplicialCone K
local notation "η" => coneApexSimplex (simplicialCone K) none
local notation "hp" => mem_coneApexSimplex (simplicialCone K) none

theorem restrict_coneHomotopyGlobal (n : ℕ) (c : Cochain L (n + 1) G) :
    restrictClosedStar L η n (coneHomotopyGlobal K n c) =
      coneHomotopy L η none hp n (restrictClosedStar L η (n + 1) c) := by
  exact restrictClosedStar_extendCarrierClosedStar L η n _

theorem coneHomotopyGlobal_apex_zero (n : ℕ) (c : Cochain L (n + 1) G)
    (τ : Simplex L n) (hτ : none ∈ τ.val) :
    coneHomotopyGlobal K n c τ = 0 := by
  let τs : ClosedStarSimplex L η n :=
    ⟨τ, simplex_mem_apexClosedStar L (simplicialCone_isConeAt K) τ⟩
  have hh := DFunLike.congr_fun (restrict_coneHomotopyGlobal K n c) τs
  exact hh.trans (coneHomotopy_apply_of_mem L η none hp n _ τs hτ)

theorem coneHomotopyGlobal_extension (n : ℕ) (c : Cochain K (n + 1) G) :
    coneHomotopyGlobal K n (bottomExtension K (n + 1) c) = 0 := by
  apply restrictClosedStar_apex_injective L (simplicialCone_isConeAt K) n
  rw [restrict_coneHomotopyGlobal, map_zero]
  apply coneHomotopy_eq_zero_of_apexFree
  intro τ hτ
  exact extension_apex_zero K (n + 1) c τ.val hτ

theorem coneHomotopyGlobal_coboundary_extension (n : ℕ) (c : Cochain K n G) :
    coneHomotopyGlobal K n (coboundary L n (bottomExtension K n c)) =
      bottomExtension K n c := by
  apply restrictClosedStar_apex_injective L (simplicialCone_isConeAt K) n
  rw [restrict_coneHomotopyGlobal]
  have hn := LinearMap.congr_fun (restrictClosedStar_coboundary (G := G) L η n)
    (bottomExtension K n c)
  simp only [LinearMap.comp_apply] at hn
  rw [hn]
  apply coneBottomReplacement_eq_self_of_apexFree
  intro τ hτ
  exact extension_apex_zero K n c τ.val hτ

theorem coneHomotopyGlobal_contraction (n : ℕ) (c : Cochain L (n + 1) G) :
    coboundary L n (coneHomotopyGlobal K n c) +
      coneHomotopyGlobal K (n + 1) (coboundary L (n + 1) c) = c := by
  apply restrictClosedStar_apex_injective L (simplicialCone_isConeAt K) (n + 1)
  rw [map_add, restrict_coneHomotopyGlobal]
  have hn := LinearMap.congr_fun (restrictClosedStar_coboundary (G := G) L η n)
    (coneHomotopyGlobal K n c)
  have hn' := LinearMap.congr_fun (restrictClosedStar_coboundary (G := G) L η (n + 1)) c
  simp only [LinearMap.comp_apply] at hn hn'
  rw [hn, hn', restrict_coneHomotopyGlobal]
  exact closedStar_contraction_positive L η none hp n _

/-- Both maps are literal additive maps between actual cochain groups. -/
def coneCoordinates (n : ℕ) : Cochain L (n + 1) G →+
    (Cochain K n G × Cochain K (n + 1) G) :=
  ((bottomRestriction K n).comp (coneHomotopyGlobal K n)).prod
    (bottomRestriction K (n + 1))

def assembleConeCoordinates (n : ℕ) :
    (Cochain K n G × Cochain K (n + 1) G) →+ Cochain L (n + 1) G where
  toFun x := coboundary L n (bottomExtension K n x.1) +
    bottomExtension K (n + 1) (x.2 - coboundary K n x.1)
  map_zero' := by simp
  map_add' x y := by
    simp only [Prod.fst_add, Prod.snd_add, map_add, map_sub]
    abel

theorem coordinates_assemble (n : ℕ) (x : Cochain K n G × Cochain K (n + 1) G) :
    coneCoordinates K n (assembleConeCoordinates K n x) = x := by
  apply Prod.ext
  · change bottomRestriction K n (coneHomotopyGlobal K n
      (coboundary L n (bottomExtension K n x.1) +
        bottomExtension K (n + 1) (x.2 - coboundary K n x.1))) = x.1
    rw [map_add, coneHomotopyGlobal_coboundary_extension,
      coneHomotopyGlobal_extension, add_zero, restriction_extension]
  · change bottomRestriction K (n + 1)
      (coboundary L n (bottomExtension K n x.1) +
        bottomExtension K (n + 1) (x.2 - coboundary K n x.1)) = x.2
    rw [map_add, restriction_coboundary, restriction_extension, restriction_extension]
    abel

theorem cone_base_boundary (n : ℕ) (c : Cochain L (n + 1) G) :
    bottomRestriction K (n + 1) c - coboundary K n (bottomRestriction K n
      (coneHomotopyGlobal K n c)) =
    bottomRestriction K (n + 1) (coneHomotopyGlobal K (n + 1)
      (coboundary L (n + 1) c)) := by
  rw [← restriction_coboundary]
  have hh := congrArg (bottomRestriction (G := G) K (n + 1))
    (coneHomotopyGlobal_contraction K n c)
  rw [map_add] at hh
  rw [← hh]
  abel

theorem assemble_coordinates (n : ℕ) (c : Cochain L (n + 1) G) :
    assembleConeCoordinates K n (coneCoordinates K n c) = c := by
  change coboundary L n (bottomExtension K n (bottomRestriction K n
      (coneHomotopyGlobal K n c))) + bottomExtension K (n + 1)
    (bottomRestriction K (n + 1) c - coboundary K n
      (bottomRestriction K n (coneHomotopyGlobal K n c))) = c
  rw [cone_base_boundary,
    extension_restriction_of_apex_zero K n _ (coneHomotopyGlobal_apex_zero K n c),
    extension_restriction_of_apex_zero K (n + 1) _
      (coneHomotopyGlobal_apex_zero K (n + 1) (coboundary L (n + 1) c))]
  exact coneHomotopyGlobal_contraction K n c

/-- The signed cone-coordinate change is proved from the actual contraction. -/
def coneCoordinatesAddEquiv (n : ℕ) : Cochain L (n + 1) G ≃+
    (Cochain K n G × Cochain K (n + 1) G) where
  toFun := coneCoordinates K n
  invFun := assembleConeCoordinates K n
  left_inv := assemble_coordinates K n
  right_inv := coordinates_assemble K n
  map_add' := (coneCoordinates K n).map_add

/-- The cone closed-cochain condition is exactly the graph of the actual
boundary coboundary in these coordinates. -/
theorem cone_closed_iff_graph (n : ℕ) (c : Cochain L (n + 1) G) :
    coboundary L (n + 1) c = 0 ↔
      (coneCoordinates K n c).2 = coboundary K n (coneCoordinates K n c).1 := by
  constructor
  · intro hc
    have hb := cone_base_boundary K n c
    rw [hc, map_zero, map_zero] at hb
    exact sub_eq_zero.mp hb
  · intro hc
    have heq := assemble_coordinates K n c
    change coboundary L n (bottomExtension K n (coneCoordinates K n c).1) +
      bottomExtension K (n + 1) ((coneCoordinates K n c).2 -
        coboundary K n (coneCoordinates K n c).1) = c at heq
    rw [hc, sub_self, map_zero, add_zero] at heq
    rw [← heq, coboundary_coboundary]

end OpenDisk.ConePhaseLiteralCoordinates
