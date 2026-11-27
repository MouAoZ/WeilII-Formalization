module

public import WeilII.AlgebraicGeometry.EtalePositiveTatePowerComparison
public import WeilII.AlgebraicGeometry.EtaleKummerConstantReduction

/-! # The normalized Kummer class under coefficient reduction -/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.Etale
open scoped CategoryTheory.Functor

namespace WeilII

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem mapKummerComposite {C D : Type*} [Category* C] [Category* D]
    (F : C ⥤ D) (S : C ⥤ C) (T : D ⥤ D) (c : S ⋙ F ⟶ F ⋙ T)
    {K M N P : C} {K' M' N' P' : D} (a : K ⟶ M) (b : M ⟶ S.obj N) (z : N ⟶ P)
    (a' : K' ⟶ M') (b' : M' ⟶ T.obj N') (z' : N' ⟶ P')
    (u : F.obj K ⟶ K') (v : F.obj M ⟶ M') (w : F.obj N ⟶ N') (r : F.obj P ⟶ P')
    (ha : F.map a ≫ v = u ≫ a') (hb : F.map b ≫ c.app N ≫ T.map w = v ≫ b')
    (hz : F.map z ≫ r = w ≫ z') :
    F.map (a ≫ b ≫ S.map z) ≫ c.app P ≫ T.map r = u ≫ a' ≫ b' ≫ T.map z' := by
  have hn := c.naturality z
  simp only [Functor.comp_map] at hn
  simp only [F.map_comp, Category.assoc]
  rw [reassoc_of% hn, ← T.map_comp, hz, T.map_comp, reassoc_of% hb, reassoc_of% ha]

/-- The power map on roots of unity and the identity on the last Kummer term take
the class of a unit to its class at the lower level, in the direct positive Tate models. -/
theorem etaleCoefficientReduction_kummerClass
    {A B : Type (u+1)} [CommRing A] [CommRing B] [NeZero (ringChar A)] [NeZero (ringChar B)]
    {ρ : A →+* B} (hρ : Function.Surjective ρ) {a : A} (ha : RingHom.ker ρ = Ideal.span {a})
    {V : Scheme.{u}} [HasInvertibleExponent A V] [HasInvertibleExponent B V]
    (v : Γ(V, ⊤)ˣ) {d : ℕ} (hd : ringChar A = ringChar B * d) :
    letI := derivedExtendScalarsCommShift hρ ha V
    let Ψ := derivedExtendScalars hρ ha V
    Ψ.map (kummerClass A v) ≫ (Ψ.commShiftIso (1 : ℤ)).hom.app _ ≫
        (derivedExtendScalarsTateObjectIso hρ ha V 1).hom⟦(1 : ℤ)⟧' =
      (derivedExtendScalarsConstantComplexIso hρ ha V).hom ≫ kummerClass B v := by
  let := derivedExtendScalarsCommShift hρ ha V
  let Ψ := derivedExtendScalars hρ ha V
  let φ := unitToGmSheaf v
  let oA := tateTwistObjectOneIso V A
  let oB := tateTwistObjectOneIso V B
  let g := kummerSequenceReductionMap ρ φ hd
  let g₁ := ShortComplex.ShortExact.singleTranspose (Sheaf.restrictScalars _ ρ)
    (derivedExtendScalarsAdjunction hρ ha V) g.τ₁
  let g₃ := ShortComplex.ShortExact.singleTranspose (Sheaf.restrictScalars _ ρ)
    (derivedExtendScalarsAdjunction hρ ha V) g.τ₃
  have h₃ : g.τ₃ = (extendScalarsToRestrictScalars ρ V).app V.constantSheafInt := by
    change (extendScalars A V).map (𝟙 _) ≫ _ = _
    rw [CategoryTheory.Functor.map_id, Category.id_comp]
    rfl
  have hu : Ψ.map (constantComplexIsoSingleFunctorExtendScalarsInt V A).hom ≫ g₃ =
      (derivedExtendScalarsConstantComplexIso hρ ha V).hom ≫
        (constantComplexIsoSingleFunctorExtendScalarsInt V B).hom := by
    dsimp only [g₃]
    rw [h₃]
    exact etaleKummerConstantReduction hρ ha V
  have hp : Ψ.map oA.inv ≫ (derivedExtendScalarsTateObjectIso hρ ha V 1).hom = g₁ ≫ oB.inv := by
    rw [positiveTateObjectReduction_eq_kummer φ hd hρ ha, ← Ψ.map_comp_assoc,
      Iso.inv_hom_id, CategoryTheory.Functor.map_id, Category.id_comp]
  have hδ := derivedExtendScalars_map_kummerδ φ hd hρ ha
    (fun x ↦ projective_sheafFiber_constantSheafInt (V.uliftPointSmallEtale x))
  change Ψ.map (kummerClassOf V A v) ≫ _ = _ ≫ kummerClassOf V B v
  rw [kummerClassOf_def, kummerClassOf_def]
  exact mapKummerComposite Ψ (shiftFunctor _ (1 : ℤ)) (shiftFunctor _ (1 : ℤ))
    (Ψ.commShiftIso (1 : ℤ)).hom _ _ _ _ _ _ _ g₃ g₁ _ hu hδ hp

end WeilII
