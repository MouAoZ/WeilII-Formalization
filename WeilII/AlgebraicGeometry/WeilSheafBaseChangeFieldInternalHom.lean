module

public import WeilConjectures.WeilSheaf.BaseChangeField.Restriction
public import WeilConjectures.WeilSheaf.StalkInternalHom
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Monoidal
import WeilConjectures.WeilSheaf.BaseChangeField.Coherence
import WeilConjectures.WeilSheaf.IhomCurry
import WeilConjectures.WeilSheaf.UpperStarLowerStarAdjunction
import WeilII.AlgebraicGeometry.WeilSheafTransportPairing

/-!
# Internal Hom of Weil sheaves after a finite extension of constants

Zhang, *On an elementary proof of Weil II*, p. 2 and Construction 2.5 on p. 3, extends the
constant field in the proof of Proposition 1.5. The internal-Hom comparison below is used to
transport the binary tensor products in the external tensor power.
-/

open AlgebraicGeometry CategoryTheory

namespace WeilII

universe u

/-- Finite extension of constants commutes with the internal Hom from a lisse Weil sheaf to a
constructible Weil sheaf, as used in Zhang, *On an elementary proof of Weil II*, pp. 2–3.

Write R for extension of constants, d for the extension degree and H for [P,Q]. The identity
#K = (#k)^d identifies the new geometric Frobenius with the d-th power of the old one under
the geometric fiber isomorphism θ. Let T be pushforward of adic modules along θ and G the
corresponding pushforward on underlying sheaves. Write F for pushforward by the inverse old
Frobenius power and B for pushforward by the inverse new Frobenius.

On underlying sheaves let e be the evaluation from H ⊗ P to Q. The one-step Weil structures
respect e by `ihom_evaluation_str`. Iterating this square by `frobeniusPowIso_tensor` and
identifying the iterates by `frobeniusPowIso_eq` gives
e ∘ (s_H ⊗ s_P) = s_Q ∘ F(e) ∘ μ_F, where s denotes the d-fold structure and μ is the
tensor comparison of the indicated functor.

The inverse Frobenius square induces τ from BG to GF. The formula `transport_obj_str` gives
the new structure t_M = G(s_M) ∘ τ_M. On underlying sheaves τ is monoidal since it consists of
two pushforward composition comparisons and the identification from the equality of scheme maps.
Set e' = G(e) ∘ μ_G. Expand e' ∘ (t_H ⊗ t_P), use naturality of μ_G, and substitute the
iterated evaluation square. The result is G(s_Q) ∘ GF(e) ∘ μ_GF ∘ (τ_H ⊗ τ_P).
Monoidality of τ moves it past μ_GF, and naturality at e moves it past GF(e). Expanding
μ_BG then gives t_Q ∘ B(e') ∘ μ_B, the required evaluation square over K.

Because θ is an isomorphism, G preserves the tensor product and its braiding, identifies the
coefficient rings, and induces the equivalence T on their modules. The inverse component at Q
of `Mod.mapModComapCompIhomIso` for P is therefore an isomorphism κ from T(H) to [T(P),T(Q)].
By `Mod.μ_comp_map_evaluation`, evaluating κ against T(P) gives exactly e'. Its square over K
thus makes κ a Weil morphism by `ProEtaleWeilSheaf.homToIhom`. Both ends are constructible
since extension preserves constructibility and RP is lisse. Lift this morphism to their full
subcategory. Its underlying adic morphism is κ, so `WeilSheaf.isIso_of_isIso_hom_hom_f`
makes it invertible there. -/
public theorem weilSheaf_baseChangeField_ihom
    {k : Type u} [Field k] [Finite k] (K : Type u) [Field K] [Finite K] [Algebra k K]
    {ℓ : ℕ} [Fact ℓ.Prime] [Fact (ringChar k ≠ ℓ)]
    {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k))] [QuasiCompact (X ↘ Spec (CommRingCat.of k))]
    (P : WeilSheaf k ℓ X) (hP : P.IsLisse) (Q : WeilSheaf k ℓ X) :
    letI : Fact (ringChar K ≠ ℓ) := ⟨(Algebra.ringChar_eq k K) ▸ Fact.out⟩
    Nonempty ((WeilSheaf.baseChangeField K).obj (P.ihom hP Q) ≅
      ((WeilSheaf.baseChangeField K).obj P).ihom (hP.baseChangeField K)
        ((WeilSheaf.baseChangeField K).obj Q)) := by
  let : Fact (ringChar K ≠ ℓ) := ⟨(Algebra.ringChar_eq k K) ▸ Fact.out⟩
  let R := WeilSheaf.baseChangeField (X := X) (k₀ := k) (l := ℓ) K
  let H := P.ihom hP Q
  let sq := WeilSheaf.isPullback_baseChangeField (k₀ := k) X K
  let θ := Scheme.Hom.geometricFiberBaseChangeIso sq
  let d := Module.finrank k K
  have hθ := Scheme.Hom.geometricFiberBaseChangeIso_hom_comp_geometricGaloisFrobenius
    sq d Module.natCard_eq_pow_finrank
  let G := ProEtale.lowerStar (WeilCoefficients.{u} ℓ) θ.hom
  let ρ := ProEtale.adicConstantSheafToLowerStar ℓ θ.hom
  have : (Mod.mapModComap (G := G) ρ).IsEquivalence := ProEtale.isEquivalence_adicLowerStar ℓ θ.hom
  let compare := Mod.mapModComapCompIhomIso ρ
    (fun _ _ ↦ Functor.LaxBraided.braided _ _) P.carrier
  let κ := compare.inv.app Q.carrier
  have evaluation := Mod.μ_comp_map_evaluation ρ
    (fun _ _ ↦ Functor.LaxBraided.braided _ _) P.carrier Q.carrier
  have pairing := weilSheaf_transport_pairing θ d hθ H P Q _
    (ProEtaleWeilSheaf.ihom_evaluation_str P.obj Q.obj)
  let m : R.obj H ⟶ (R.obj P).ihom (hP.baseChangeField K) (R.obj Q) :=
    ObjectProperty.homMk (ProEtaleWeilSheaf.homToIhom (R.obj H).obj (R.obj P).obj
      (R.obj Q).obj κ (by
        erw [← evaluation]
        exact pairing))
  have : IsIso m.hom.hom.f := inferInstanceAs (IsIso (compare.inv.app Q.carrier))
  have : IsIso m := WeilSheaf.isIso_of_isIso_hom_hom_f m
  exact ⟨asIso m⟩

end WeilII
