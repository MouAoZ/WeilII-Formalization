module

public import WeilConjectures.WeilSheaf.BaseChangeField.Transport
public import WeilConjectures.WeilSheaf.StalkPairing
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.MonoidalIso
import WeilII.CategoryTheory.LaxMonoidalPairingTransport
import WeilII.AlgebraicGeometry.CompactificationComponentTransport
import WeilConjectures.WeilSheaf.BaseChangeField.Stalk

open AlgebraicGeometry CategoryTheory MonoidalCategory Functor.LaxMonoidal
open AlgebraicGeometry.ProEtale

namespace WeilII

universe u

/-- Transport a Frobenius-compatible pairing along an identification of geometric fibers
taking an old Frobenius power to the new Frobenius. This is the pairing calculation for
the finite extension of constants on p. 2 of Zhang, *On an elementary proof of Weil II*.
The iterated structures preserve the pairing. The monoidal exchange of the two pushforwards
takes their pairing square to the one for the transported structures. -/
public theorem weilSheaf_transport_pairing
    {k K : Type u} [Field k] [Finite k] [Field K] [Finite K] {ℓ : ℕ}
    [Fact ℓ.Prime] [Fact (ringChar k ≠ ℓ)]
    {X Y : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of K))]
    (θ : (X ↘ Spec (.of k)).geometricFiber ≅ (Y ↘ Spec (.of K)).geometricFiber)
    (d : ℕ) (hθ : θ.hom ≫ (Y ↘ Spec (.of K)).geometricGaloisFrobenius.asIso.hom =
      ((X ↘ Spec (.of k)).geometricGaloisFrobenius ^ d).asIso.hom ≫ θ.hom)
    (A P Q : WeilSheaf k ℓ X) (e : A.obj.carrier.X ⊗ P.obj.carrier.X ⟶ Q.obj.carrier.X)
    (he : (A.obj.str.hom.hom ⊗ₘ P.obj.str.hom.hom) ≫ e =
      μ ((X ↘ Spec (.of k)).geometricGaloisFrobenius.asIso.inv)_*[WeilCoefficients.{u} ℓ] _ _ ≫
        ((X ↘ Spec (.of k)).geometricGaloisFrobenius.asIso.inv)_*[_].map e ≫ Q.obj.str.hom.hom) :
    let R := ProEtaleWeilSheaf.transport (l := ℓ) θ d hθ
    let G := (θ.hom)_*[WeilCoefficients.{u} ℓ]
    let Fr := ((Y ↘ Spec (.of K)).geometricGaloisFrobenius.asIso.inv)_*[WeilCoefficients.{u} ℓ]
    let e' := μ G A.obj.carrier.X P.obj.carrier.X ≫ G.map e
    ((R.obj A.obj).str.hom.hom ⊗ₘ (R.obj P.obj).str.hom.hom) ≫ e' =
      μ Fr (G.obj A.obj.carrier.X) (G.obj P.obj.carrier.X) ≫ Fr.map e' ≫
        (R.obj Q.obj).str.hom.hom := by
  intro R G Fr e'
  let f := ((X ↘ Spec (.of k)).geometricGaloisFrobenius ^ d).asIso.inv
  let g := (Y ↘ Spec (.of K)).geometricGaloisFrobenius.asIso.inv
  let ψ := lowerStarComp (WeilCoefficients.{u} ℓ) θ.hom g ≪≫
    lowerStarCongr (WeilCoefficients.{u} ℓ)
      (ProEtaleWeilSheaf.hom_comp_geometricGaloisFrobenius_inv θ d hθ) ≪≫
    (lowerStarComp (WeilCoefficients.{u} ℓ) f θ.hom).symm
  have : NatTrans.IsMonoidal ψ.hom := by
    dsimp only [ψ, Iso.trans_hom, Iso.symm_hom]
    infer_instance
  have str (M : WeilSheaf k ℓ X) : (R.obj M.obj).str.hom.hom =
      ψ.hom.app M.obj.carrier.X ≫ G.map (M.frobeniusPowIso d).hom.hom := by
    rw [WeilSheaf.frobeniusPowIso_eq]
    simp only [ψ, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Category.assoc]
    transport_compactification_component
      (ProEtaleWeilSheaf.forget_map_transport_obj_str_hom θ d hθ M.obj)
  have power := WeilSheaf.frobeniusPowIso_tensor A P Q e he d
  dsimp only [e']
  rw [str, str, str]
  exact laxMonoidal_map_equivariant_pairing G (f)_*[WeilCoefficients.{u} ℓ] Fr ψ.hom
    (A.frobeniusPowIso d).hom.hom (P.frobeniusPowIso d).hom.hom (Q.frobeniusPowIso d).hom.hom
    e power

end WeilII
