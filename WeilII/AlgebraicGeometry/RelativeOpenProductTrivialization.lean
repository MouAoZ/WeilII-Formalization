module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.AlgebraicGeometry.Restrict

/-! # Base change of a product chart for an open subscheme -/

namespace WeilII

open AlgebraicGeometry CategoryTheory Limits

universe u

private theorem productOpenIso {B P S : Scheme.{u}} (d : B ⟶ S) (π : P ⟶ S) (U : P.Opens)
    (σ : pullback d π ≅ pullback d π) (C : (pullback d π).Opens)
    (hc : C = σ.hom ⁻¹ᵁ (pullback.snd d π ⁻¹ᵁ U)) :
    let i := pullback.map d (U.ι ≫ π) d π (𝟙 _) U.ι (𝟙 _) (by simp) (by simp)
    ∃ e : C.toScheme ≅ pullback d (U.ι ≫ π), e.hom ≫ i = C.ι ≫ σ.hom := by
  intro i
  let q := pullback.snd d π
  let α := pullbackLeftPullbackSndIso d π U.ι
  have fac : α.hom ≫ i = pullback.fst q U.ι := by
    apply pullback.hom_ext
    · simp [α, i, q]
    · simp [α, i, q, pullback.condition]
  refine ⟨(pullback d π).isoOfEq hc ≪≫ σ.hom.preimageIso (q ⁻¹ᵁ U) ≪≫
    (pullbackRestrictIsoRestrict q U).symm ≪≫ α, ?_⟩
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, fac,
    pullbackRestrictIsoRestrict_inv_fst, Scheme.Hom.preimageIso_hom_ι]
  exact Scheme.isoOfEq_hom_ι_assoc _ hc _

/-- An automorphism of a product over its first projection identifies an open with the
product of the first factor and an open of the second factor if it identifies the
underlying opens. Both identifications pull back along every map to the first factor. -/
public theorem relativeOpenProductTrivialization {B P S : Scheme.{u}} (d : B ⟶ S) (π : P ⟶ S)
    (U : P.Opens) (σ : pullback d π ≅ pullback d π)
    (hp : σ.hom ≫ pullback.fst d π = pullback.fst d π) (C : (pullback d π).Opens)
    (hc : C = σ.hom ⁻¹ᵁ (pullback.snd d π ⁻¹ᵁ U)) :
    let v := U.ι ≫ π
    let i := pullback.map d v d π (𝟙 _) U.ι (𝟙 _) (by simp) (by simp [v])
    ∃ e : C.toScheme ≅ pullback d v, e.hom ≫ i = C.ι ≫ σ.hom ∧
      ∀ (T : Scheme.{u}) (h : T ⟶ B),
        let t := h ≫ d
        let H := pullback.map t π d π h (𝟙 _) (𝟙 _) (by simp [t]) (by simp)
        let Hopen := pullback.map t v d v h (𝟙 _) (𝟙 _) (by simp [t]) (by simp)
        let iT := pullback.map t v t π (𝟙 _) U.ι (𝟙 _) (by simp) (by simp [v])
        ∃ (σT : pullback t π ≅ pullback t π) (eT : (H ⁻¹ᵁ C).toScheme ≅ pullback t v),
          σT.hom ≫ pullback.fst t π = pullback.fst t π ∧ σT.hom ≫ H = H ≫ σ.hom ∧
          eT.hom ≫ iT = (H ⁻¹ᵁ C).ι ≫ σT.hom ∧
          eT.hom ≫ Hopen = (H ∣_ C) ≫ e.hom := by
  intro v i
  obtain ⟨e, he⟩ := productOpenIso d π U σ C hc
  change e.hom ≫ i = C.ι ≫ σ.hom at he
  refine ⟨e, he, ?_⟩
  intro T h t H Hopen iT
  let p := pullback.fst d π
  let pT := pullback.fst t π
  have pb : IsPullback pT H h p := by
    apply IsPullback.of_bot (t := IsPullback.of_hasPullback d π)
    · simpa [H, pT, t] using IsPullback.of_hasPullback t π
    · simp [H, pT]
  have hp' : σ.inv ≫ p = p := by rw [Iso.inv_comp_eq]; exact hp.symm
  let lift (m : pullback d π ⟶ pullback d π) (hm : m ≫ p = p) :=
    pb.lift pT (H ≫ m) (by rw [Category.assoc, hm, pb.w])
  have cancel (m n : pullback d π ⟶ pullback d π) (hm : m ≫ p = p) (hn : n ≫ p = p)
      (hmn : m ≫ n = 𝟙 _) : lift m hm ≫ lift n hn = 𝟙 _ := by
    apply pb.hom_ext
    · simp [lift]
    · simp [lift, hmn]
  let σT : pullback t π ≅ pullback t π :=
    ⟨lift σ.hom hp, lift σ.inv hp', cancel _ _ hp hp' σ.hom_inv_id,
      cancel _ _ hp' hp σ.inv_hom_id⟩
  have comm : σT.hom ≫ H = H ≫ σ.hom := pb.lift_snd ..
  have qcomm : H ≫ pullback.snd d π = pullback.snd t π := by simp [H]
  have hcT : H ⁻¹ᵁ C = σT.hom ⁻¹ᵁ (pullback.snd t π ⁻¹ᵁ U) := by
    rw [hc, ← Scheme.Hom.comp_preimage, ← comm, Scheme.Hom.comp_preimage,
      ← Scheme.Hom.comp_preimage H, qcomm]
  obtain ⟨eT, heT⟩ := productOpenIso t π U σT _ hcT
  change eT.hom ≫ iT = (H ⁻¹ᵁ C).ι ≫ σT.hom at heT
  refine ⟨σT, eT, pb.lift_fst .., comm, heT, ?_⟩
  have ei : i = e.inv ≫ C.ι ≫ σ.hom := (e.eq_inv_comp).mpr he
  have : Mono i := by rw [ei]; infer_instance
  have square : Hopen ≫ i = iT ≫ H := by apply pullback.hom_ext <;> simp [Hopen, H, iT, i]
  apply (cancel_mono i).mp
  rw [Category.assoc, square, ← Category.assoc, heT, Category.assoc, comm,
    Category.assoc, he, morphismRestrict_ι_assoc]

end WeilII

