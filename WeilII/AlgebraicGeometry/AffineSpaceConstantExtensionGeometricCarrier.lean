module

public import WeilII.Paper.ExternalTensorPowerConstantFieldExtension
import WeilConjectures.Mathlib.FieldTheory.Finite.Basic

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace WeilII

universe u

set_option backward.isDefEq.respectTransparency false in
/-- In Zhang's change of constants (p. 2), a specified embedding of the finite extension
into the old algebraic closure gives affine-space coordinates for the new geometric fiber.
The extended sheaf in these coordinates has the original geometric carrier. To match the
specified embedding, compose the closure isomorphism used in restriction of constants with
a power of geometric Frobenius. Its effect on the old carrier is the iterated Weil structure. -/
public theorem exists_affineSpaceBaseChangeField_geometricCarrier
    {k : Type u} [Field k] [Finite k] (K : IntermediateField k (AlgebraicClosure k))
    [Finite K] {ℓ : ℕ} [Fact ℓ.Prime] [Fact (ringChar k ≠ ℓ)] [Fact (ringChar K ≠ ℓ)]
    (I : Type u) (H : WeilSheaf k ℓ 𝔸(I; Spec (.of k))) :
    let T := Spec (.of (AlgebraicClosure k))
    let S := Spec (.of K)
    let X := 𝔸(I; S)
    let a := X ↘ S
    let b := AffineSpace.map I (Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure k))))
    let h := (AffineSpace.isPullback_map (n := I) (Scheme.specAlgebraicClosure k).hom).isoPullback
    ∃ (v : 𝔸(I; T) ≅ a.geometricFiber) (t : T ≅ Spec (.of (AlgebraicClosure K))),
      v.hom ≫ a.geometricFiberProj = b ∧
      v.hom ≫ a.geometricFiberToAlgebraicClosure = (𝔸(I; T) ↘ T) ≫ t.hom ∧
      Nonempty ((ProEtale.adicUpperStar ℓ v.hom).obj (affineSpaceWeilSheafBaseChangeField K H).carrier ≅
        (ProEtale.adicUpperStar ℓ h.hom).obj H.carrier) := by
  classical
  intro T S X a b h
  let := Fintype.ofFinite k
  let τ := algebraicClosureAlgEquiv k K
  let emb := Scheme.Hom.algebraicClosureEmbedding (k₀ := k) (k₀' := K)
  have hem : emb.comp (algebraMap k K) =
      (algebraMap K (AlgebraicClosure k)).comp (algebraMap k K) := by
    ext x
    exact (Scheme.Hom.algebraicClosureEmbedding_algebraMap x).trans
      (IsScalarTower.algebraMap_apply k K (AlgebraicClosure k) x)
  obtain ⟨r, hr⟩ := FiniteField.exists_apply_eq_pow_card_pow_of_comp_eq _ hem
  have hc : Nat.card K = Fintype.card k ^ Module.finrank k K := by
    rw [Module.natCard_eq_pow_finrank (K := k), Nat.card_eq_fintype_card]
  obtain ⟨m, _, hm⟩ := FiniteField.exists_geometricFrobeniusAlgEquivOfAlgebraic_pow_apply_eq k
    (AlgebraicClosure k) Module.finrank_pos hc emb r
  let φ := FiniteField.geometricFrobeniusAlgEquivOfAlgebraic k (AlgebraicClosure k) ^ m
  let δ := τ.trans φ
  let t := Scheme.Spec.mapIso δ.toRingEquiv.toCommRingCatIso.op
  have ht : t.hom ≫ (Scheme.specAlgebraicClosure K).hom =
      Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure k))) :=
    spec_map_comp_spec_map_eq _ _ _ fun x ↦ (hm x).trans (hr x).symm
  let v₀ := (AffineSpace.functor.obj (Opposite.op I)).mapIso t
  let sq := AffineSpace.isPullback_map (n := I) (Scheme.specAlgebraicClosure K).hom
  let v := v₀ ≪≫ sq.isoPullback
  have hv₁ : v.hom ≫ a.geometricFiberProj = b := by
    change (_ ≫ _) ≫ pullback.fst _ _ = _
    erw [Category.assoc, sq.isoPullback_hom_fst]
    exact (AffineSpace.map_comp t.hom _).symm.trans (congrArg (AffineSpace.map I) ht)
  have hv₂ : v.hom ≫ a.geometricFiberToAlgebraicClosure = (𝔸(I; T) ↘ T) ≫ t.hom := by
    change (_ ≫ _) ≫ pullback.snd _ _ = _
    erw [Category.assoc, sq.isoPullback_hom_snd]
    exact AffineSpace.map_over t.hom
  refine ⟨v, t, hv₁, hv₂, ?_⟩
  let a₀ := 𝔸(I; Spec (.of k)) ↘ Spec (.of k)
  let θ := Scheme.Hom.geometricFiberBaseChangeIso
    (WeilSheaf.isPullback_baseChangeField (k₀ := k) 𝔸(I; Spec (.of k)) K)
  let c := affineSpaceBaseChangeFieldIso k K I
  let f := Scheme.Hom.geometricFiberMap c.hom (comp_over c.hom S)
  let Fr := (a₀.geometricGaloisFrobenius ^ m).asIso
  let z := WeilSheaf.isPullback_baseChangeField (k₀ := k) 𝔸(I; Spec (.of k)) K
  let a' := (𝔸(I; Spec (.of k))).baseChangeField k K ↘ S
  have θ₁ : θ.inv ≫ a₀.geometricFiberProj =
      a'.geometricFiberProj ≫ pullback.fst _ _ :=
    Scheme.Hom.geometricFiberBaseChangeInv_comp_geometricFiberProj z
  have θ₂ : θ.inv ≫ a₀.geometricFiberToAlgebraicClosure =
      a'.geometricFiberToAlgebraicClosure ≫ Spec.map (CommRingCat.ofHom τ.symm.toRingHom) :=
    Scheme.Hom.geometricFiberBaseChangeInv_comp_geometricFiberToAlgebraicClosure z
  have f₁ : f ≫ a'.geometricFiberProj = a.geometricFiberProj ≫ c.hom :=
    Scheme.Hom.geometricFiberMap_comp_geometricFiberProj _ _
  have f₂ : f ≫ a'.geometricFiberToAlgebraicClosure = a.geometricFiberToAlgebraicClosure :=
    Scheme.Hom.geometricFiberMap_comp_geometricFiberToAlgebraicClosure _ _
  have h₁ : h.hom ≫ a₀.geometricFiberProj = AffineSpace.map I (Scheme.specAlgebraicClosure k).hom :=
    (AffineSpace.isPullback_map _).isoPullback_hom_fst
  have h₂ : h.hom ≫ a₀.geometricFiberToAlgebraicClosure = 𝔸(I; T) ↘ T :=
    (AffineSpace.isPullback_map _).isoPullback_hom_snd
  have Fr₁ : Fr.hom ≫ a₀.geometricFiberProj = a₀.geometricFiberProj :=
    Scheme.Hom.geometricGaloisFrobenius_pow_hom_comp_geometricFiberProj _ _
  have Fr₂ : Fr.hom ≫ a₀.geometricFiberToAlgebraicClosure =
      a₀.geometricFiberToAlgebraicClosure ≫ (specGeometricFrobenius k ^ m).asIso.hom :=
    Scheme.Hom.geometricGaloisFrobenius_pow_hom_comp_geometricFiberToAlgebraicClosure _ _
  have c₁ : c.hom ≫ pullback.fst _ _ =
      AffineSpace.map I (Spec.map (CommRingCat.ofHom (algebraMap k K))) :=
    (AffineSpace.isPullback_map _).isoPullback_hom_fst
  have w : v.hom ≫ f ≫ θ.inv = h.hom ≫ Fr.hom := by
    apply pullback.hom_ext
    · change _ ≫ a₀.geometricFiberProj = _ ≫ a₀.geometricFiberProj
      simp only [Category.assoc, θ₁, reassoc_of% f₁, reassoc_of% hv₁, Fr₁, h₁, c₁]
      change AffineSpace.map I _ ≫ AffineSpace.map I _ = AffineSpace.map I _
      rw [← AffineSpace.map_comp]
      exact congrArg (AffineSpace.map I) (spec_map_comp_spec_map_eq _ _ _
        fun x ↦ (IsScalarTower.algebraMap_apply k K (AlgebraicClosure k) x).symm)
    · change _ ≫ a₀.geometricFiberToAlgebraicClosure = _ ≫ a₀.geometricFiberToAlgebraicClosure
      simp only [Category.assoc, θ₂, reassoc_of% f₂, reassoc_of% hv₂, Fr₂, reassoc_of% h₂]
      rw [specGeometricFrobenius_pow_hom]
      exact congrArg ((𝔸(I; T) ↘ T) ≫ ·) (spec_map_comp_spec_map_eq _ _ _ fun x ↦ by
        change φ (τ (τ.symm x)) = φ x
        rw [τ.apply_symm_apply])
  let pull {A B : Scheme.{u}} (g : A ⟶ B) := ProEtale.adicUpperStar ℓ g
  let aθ := (ProEtale.adicUpperStarIsoLowerStarInv ℓ θ.symm).symm.app H.carrier
  let eFr := (ProEtale.adicUpperStarIsoLowerStarInv ℓ Fr).app H.carrier ≪≫ H.frobeniusPowIso m
  refine ⟨(pull v.hom).mapIso ((pull f).mapIso aθ) ≪≫ ?_⟩
  exact (pull v.hom).mapIso ((ProEtale.adicUpperStarComp ℓ f θ.inv).symm.app _) ≪≫
    (ProEtale.adicUpperStarComp ℓ v.hom (f ≫ θ.inv)).symm.app _ ≪≫
    (ProEtale.adicUpperStarCongr ℓ w).app _ ≪≫
    (ProEtale.adicUpperStarComp ℓ h.hom Fr.hom).app _ ≪≫ (pull h.hom).mapIso eFr

end WeilII
