import Formalization.OpenDisk.PhaseDuality

/-! Divisible real-circle characters separate integral chains modulo every subgroup. -/
noncomputable section
namespace GeneralSphereT.Transport
open OpenDisk.PhaseDuality
variable {A : Type*} [AddCommGroup A]

theorem circle_separates {x : A} (hx : x≠0) : ∃ χ : A →ₗ[ℤ] Phase, χ x≠0 := by
  let n := addOrderOf x
  let N := if n=0 then 2 else n
  have hN : 0<N := by dsimp [N]; split <;> omega
  have hN' : N≠1 := by
    have h : n≠1 := fun e => hx (AddMonoid.addOrderOf_eq_one_iff.mp e)
    dsimp [N]
    split <;> omega
  have div : N ∣ n := by dsimp [N]; split <;> simp_all
  let t : Phase := ((1/(N:ℝ) : ℝ) : Phase)
  have ht : addOrderOf t=N := AddCircle.addOrderOf_period_div (p:=(1:ℝ)) hN
  have ht' : t≠0 := fun e => hN' (ht.symm.trans (AddMonoid.addOrderOf_eq_one_iff.mpr e))
  let f := LinearMap.toSpanSingleton ℤ A x
  let g := LinearMap.toSpanSingleton ℤ Phase t
  have ann : g ∈ annihilator (LinearMap.ker f) := by
    intro k hk
    change k • x=0 at hk
    change k • t=0
    apply addOrderOf_dvd_iff_zsmul_eq_zero.mp
    rw [ht]
    exact (Int.natCast_dvd_natCast.mpr div).trans (addOrderOf_dvd_iff_zsmul_eq_zero.mpr hk)
  obtain ⟨χ,hχ⟩ := (annihilates_kernel_iff f g).mp ann
  have e := LinearMap.congr_fun hχ 1
  have eq : χ x=t := by simpa [f,g] using e
  exact ⟨χ,eq ▸ ht'⟩

theorem mem_iff_annihilator (S : Submodule ℤ A) (x : A) :
    x ∈ S ↔ ∀ χ : A →ₗ[ℤ] Phase, χ ∈ annihilator S → χ x=0 := by
  constructor
  · exact fun h χ hχ => hχ x h
  · contrapose!
    intro h
    have hn : S.mkQ x≠0 := fun e => h ((Submodule.Quotient.mk_eq_zero S).mp e)
    obtain ⟨χ,hχ⟩ := circle_separates hn
    refine ⟨χ.comp S.mkQ,fun y hy => ?_,hχ⟩
    change χ (S.mkQ y)=0
    rw [show S.mkQ y=0 from (Submodule.Quotient.mk_eq_zero S).mpr hy,map_zero]

/-- Integral maps are isomorphisms precisely when their real-circle character pullbacks are. -/
theorem dual_bijective_iff {B : Type*} [AddCommGroup B] (f : A →ₗ[ℤ] B) :
    Function.Bijective (fun χ : B →ₗ[ℤ] Phase => χ.comp f) ↔ Function.Bijective f := by
  constructor
  · rintro ⟨hin,hsur⟩
    constructor
    · intro a b hab
      by_contra ne
      obtain ⟨ψ,hψ⟩ := circle_separates (sub_ne_zero.mpr ne)
      obtain ⟨χ,rfl⟩ := hsur ψ
      apply hψ
      simp [map_sub,hab]
    · intro y
      by_contra hn
      have hy : y ∉ LinearMap.range f := hn
      have no := mt (mem_iff_annihilator (LinearMap.range f) y).mpr hy
      push_neg at no
      obtain ⟨χ,hχ,ne⟩ := no
      have h : χ.comp f = (0 : B →ₗ[ℤ] Phase).comp f := by
        ext x
        exact hχ (f x) ⟨x,rfl⟩
      exact ne (by rw [hin h]; rfl)
  · intro hf
    let e := LinearEquiv.ofBijective f hf
    refine ⟨fun a b h => LinearMap.ext (fun y => ?_),fun ψ => ⟨ψ.comp e.symm.toLinearMap,?_⟩⟩
    · obtain ⟨x,rfl⟩ := hf.2 y
      exact LinearMap.congr_fun h x
    · ext x
      exact congrArg ψ (e.symm_apply_apply x)
end GeneralSphereT.Transport
