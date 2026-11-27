module

public import WeilII.AlgebraicGeometry.AdicInvariantPresentation
public import WeilConjectures.WeilSheaf.BaseChangeField.Stalk

/-! # Invariant presentations under geometric pullback and transport of Weil sheaves -/

@[expose] public section

open AlgebraicGeometry CategoryTheory AlgebraicGeometry.ProEtale

namespace WeilII.AdicInvariantPresentation

universe u

variable {k : Type u} [Field k] [Finite k] {ℓ : ℕ} [Fact ℓ.Prime] [Fact (ringChar k ≠ ℓ)]
variable {Y : Scheme.{u}} [Y.Over (Spec (CommRingCat.of k))]
variable {S : Scheme.{u}} {E : AdicSheaf ℓ S} (F : WeilSheaf k ℓ Y)

local notation "Fr(" Y "," k ")" => Scheme.Hom.geometricGaloisFrobenius (Y ↘ Spec (CommRingCat.of k))
local notation "geom(" Y "," k ")" => Scheme.Hom.geometricFiber (Y ↘ Spec (CommRingCat.of k))

theorem weilPullSquare {Z : Scheme.{u}} [Z.Over (Spec (CommRingCat.of k))]
    (i : Z ⟶ Y) [i.IsOver (Spec (CommRingCat.of k))] :
    Square (Scheme.Hom.geometricFiberMap i (comp_over i _))
      (Scheme.Hom.geometricFiberMap_comp_geometricGaloisFrobenius i (comp_over i _)).symm
      F.frobeniusStr ((WeilSheaf.upperStar i).obj F).frobeniusStr (𝟙 _) :=
  WeilSheaf.upperStar_frobeniusStr_compatible i F

/-- Pull back a presentation of F along a morphism of schemes over a finite field.
The geometric pullback comparison for the Weil structure supplies the exchange square. -/
noncomputable def weilPull {Z : Scheme.{u}} [Z.Over (Spec (CommRingCat.of k))]
    (i : Z ⟶ Y) [i.IsOver (Spec (CommRingCat.of k))]
    {p : geom(Y,k) ⟶ S} {hp : Fr(Y,k).asIso.hom ≫ p = p}
    (P : AdicInvariantPresentation p hp E F.obj.carrier F.frobeniusStr)
    {q : geom(Z,k) ⟶ S} (hj : Scheme.Hom.geometricFiberMap i (comp_over i _) ≫ p = q)
    (hq : Fr(Z,k).asIso.hom ≫ q = q) :
    AdicInvariantPresentation q hq E ((WeilSheaf.upperStar i).obj F).obj.carrier
      ((WeilSheaf.upperStar i).obj F).frobeniusStr :=
  P.pull _ hj hq (Scheme.Hom.geometricFiberMap_comp_geometricGaloisFrobenius i (comp_over i _)).symm
    (Iso.refl _) (𝟙 _) rfl (weilPullSquare F i)

theorem square_of_weil_compatibility {K : Type u} [Field K] [Finite K] [Fact (ringChar K ≠ ℓ)]
    {Z : Scheme.{u}} [Z.Over (Spec (CommRingCat.of K))] (G : WeilSheaf K ℓ Z)
    (j : geom(Z,K) ⟶ geom(Y,k)) (d : ℕ)
    (sq : j ≫ (Fr(Y,k) ^ d).asIso.hom = Fr(Z,K).asIso.hom ≫ j)
    (z : (j)^*[WeilCoefficients.{u} ℓ].obj F.obj.carrier.X ⟶ G.obj.carrier.X)
    (h : (upperStarComp _ Fr(Z,K).asIso.hom j).hom.app F.obj.carrier.X ≫
        (Fr(Z,K).asIso.hom)^*[_].map z ≫ G.frobeniusStr =
      (upperStarCongr _ sq.symm).hom.app F.obj.carrier.X ≫
        (upperStarComp _ j (Fr(Y,k) ^ d).asIso.hom).hom.app F.obj.carrier.X ≫
        (j)^*[_].map (F.frobeniusPowStr d) ≫ z) :
    Square j sq.symm (F.frobeniusPowStr d) G.frobeniusStr z :=
  -- The upstream square uses the commutative-ring instance for the pullback comparisons.
  -- Spell out its coefficient category to share those comparisons with the imported theorem.
  @square_of_other_instance (WeilCoefficients.{u} ℓ)
    (@ModuleCat.moduleCategory.{u+1} (ULift.{u+1} (PadicAlgCl ℓ)) _)
    (@ModuleCat.abelian.{u+1} (ULift.{u+1} (PadicAlgCl ℓ)) _)
    (instIsGrothendieckAbelianModuleCat (ULift.{u+1} (PadicAlgCl ℓ)))
    (ModuleCat.isGrothendieckAbelian_of_commRing (ULift.{u+1} (PadicAlgCl ℓ)))
    _ _ _ j _ sq.symm F.obj.carrier.X G.obj.carrier.X (F.frobeniusPowStr d) G.frobeniusStr z h

theorem weilTransportSquare {K : Type u} [Field K] [Finite K] [Fact (ringChar K ≠ ℓ)]
    {Z : Scheme.{u}} [Z.Over (Spec (CommRingCat.of K))]
    (θ : geom(Y,k) ≅ geom(Z,K)) (d : ℕ)
    (hθ : θ.hom ≫ Fr(Z,K).asIso.hom = (Fr(Y,k) ^ d).asIso.hom ≫ θ.hom) :
    Square θ.symm.hom (WeilSheaf.symm_hom_comp_geometricGaloisFrobenius_pow hθ).symm
      (F.frobeniusPowStr d) ((WeilSheaf.transport θ d hθ).obj F).frobeniusStr
      ((upperStarIsoLowerStarInv _ θ.symm).hom.app F.obj.carrier.X) :=
  square_of_weil_compatibility F ((WeilSheaf.transport θ d hθ).obj F) θ.symm.hom d
    (WeilSheaf.symm_hom_comp_geometricGaloisFrobenius_pow hθ) _
    (WeilSheaf.transport_frobeniusStr_compatible hθ F)

/-- Transport a presentation for the d-th Frobenius power along an identification of
geometric fibers. Pullback by the inverse agrees with pushforward by the identification. -/
noncomputable def weilTransport {K : Type u} [Field K] [Finite K] [Fact (ringChar K ≠ ℓ)]
    {Z : Scheme.{u}} [Z.Over (Spec (CommRingCat.of K))]
    (θ : geom(Y,k) ≅ geom(Z,K)) (d : ℕ)
    (hθ : θ.hom ≫ Fr(Z,K).asIso.hom = (Fr(Y,k) ^ d).asIso.hom ≫ θ.hom)
    {p : geom(Y,k) ⟶ S} {hp : (Fr(Y,k) ^ d).asIso.hom ≫ p = p}
    (P : AdicInvariantPresentation p hp E F.obj.carrier (F.frobeniusPowStr d))
    {q : geom(Z,K) ⟶ S} (hj : θ.symm.hom ≫ p = q) (hq : Fr(Z,K).asIso.hom ≫ q = q) :
    AdicInvariantPresentation q hq E ((WeilSheaf.transport θ d hθ).obj F).obj.carrier
      ((WeilSheaf.transport θ d hθ).obj F).frobeniusStr :=
  P.pull θ.symm.hom hj hq (WeilSheaf.symm_hom_comp_geometricGaloisFrobenius_pow hθ).symm
    ((adicUpperStarIsoLowerStarInv ℓ θ.symm).app F.obj.carrier)
    ((upperStarIsoLowerStarInv _ θ.symm).hom.app F.obj.carrier.X)
    (adicUpperStarIsoLowerStarInv_hom_app_hom θ.symm F.obj.carrier)
    (weilTransportSquare F θ d hθ)

/-- Restricting the field of an arithmetic sheaf presents its Weil sheaf by the
composite of the two projections to the original arithmetic scheme. -/
noncomputable def restriction {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k))]
    (K : Type u) [Field K] [Finite K] [Algebra k K] [Fact (ringChar K ≠ ℓ)]
    {E : AdicSheaf ℓ X} (hE : IsAdicLisseSheaf E) :
    let π := Limits.pullback.fst (X ↘ Spec (CommRingCat.of k))
      (Spec.map (CommRingCat.ofHom (algebraMap k K)))
    let p := (X.baseChangeField k K ↘ Spec (CommRingCat.of K)).geometricFiberProj
    let G := (WeilSheaf.baseChangeField (X := X) K).obj (WeilSheaf.geometricFiberPullback (k₀ := k) hE)
    AdicInvariantPresentation (p ≫ π)
      (Scheme.Hom.geometricGaloisFrobenius_hom_comp_geometricFiberProj_assoc _ _)
      E G.obj.carrier G.frobeniusStr := by
  let sq := WeilSheaf.isPullback_baseChangeField (k₀ := k) X K
  let θ := Scheme.Hom.geometricFiberBaseChangeIso sq
  let d := Module.finrank k K
  have hθ := Scheme.Hom.geometricFiberBaseChangeIso_hom_comp_geometricGaloisFrobenius sq d
    Module.natCard_eq_pow_finrank
  exact weilTransport (Z := X.baseChangeField k K) (WeilSheaf.geometricFiberPullback (k₀ := k) hE)
    θ d hθ (geometricPow (k := k) hE d Module.finrank_pos)
    (Scheme.Hom.geometricFiberBaseChangeInv_comp_geometricFiberProj sq)
    (Scheme.Hom.geometricGaloisFrobenius_hom_comp_geometricFiberProj_assoc _ _)

/-- If a Weil sheaf on Y comes from E over an arithmetic model S, its pullback
along i is the canonical geometric Weil sheaf of the arithmetic pullback along f. -/
noncomputable def arithmeticPullIso {S : Scheme.{u}} {E : AdicSheaf ℓ S}
    (hE : IsAdicLisseSheaf E) {Z : Scheme.{u}} [Z.Over (Spec (CommRingCat.of k))]
    (i : Z ⟶ Y) [i.IsOver (Spec (CommRingCat.of k))]
    (π : Y ⟶ S) (f : Z ⟶ S) (hi : i ≫ π = f)
    (T : AdicInvariantPresentation ((Y ↘ Spec (CommRingCat.of k)).geometricFiberProj ≫ π)
      (Scheme.Hom.geometricGaloisFrobenius_hom_comp_geometricFiberProj_assoc _ _)
      E F.obj.carrier F.frobeniusStr) :
    (WeilSheaf.upperStar i).obj F ≅
      WeilSheaf.geometricFiberPullback (k₀ := k) (IsAdicLisseSheaf.upperStar f hE) := by
  let pZ := (Z ↘ Spec (CommRingCat.of k)).geometricFiberProj
  let pY := (Y ↘ Spec (CommRingCat.of k)).geometricFiberProj
  let j := Scheme.Hom.geometricFiberMap i (comp_over i (Spec (CommRingCat.of k)))
  have hj : j ≫ (pY ≫ π) = pZ ≫ f := by
    rw [← Category.assoc, show j ≫ pY = pZ ≫ i from
      Scheme.Hom.geometricFiberMap_comp_geometricFiberProj _ _, Category.assoc, hi]
  have hc : Fr(Z,k).asIso.hom ≫ (pZ ≫ f) = pZ ≫ f :=
    Scheme.Hom.geometricGaloisFrobenius_hom_comp_geometricFiberProj_assoc _ _
  exact weilIso (F := (WeilSheaf.upperStar i).obj F)
    (G := WeilSheaf.geometricFiberPullback (k₀ := k) (IsAdicLisseSheaf.upperStar f hE))
    (weilPull F i T hj hc)
    (compModel f E (geometric (k := k) (IsAdicLisseSheaf.upperStar f hE)) rfl hc)

/-- Pulling an arithmetic sheaf to a finite extension and then to its geometric
fiber agrees, as a Weil sheaf, with restricting its canonical Weil sheaf and
pulling back along the given morphism to the fiber product. -/
theorem arithmeticBaseChange {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k))]
    (K : Type u) [Field K] [Finite K] [Algebra k K] [Fact (ringChar K ≠ ℓ)]
    {Z : Scheme.{u}} [Z.Over (Spec (CommRingCat.of K))]
    (i : Z ⟶ X.baseChangeField k K) [i.IsOver (Spec (CommRingCat.of K))]
    (f : Z ⟶ X) (hi : i ≫ Limits.pullback.fst (X ↘ Spec (CommRingCat.of k))
      (Spec.map (CommRingCat.ofHom (algebraMap k K))) = f)
    {H : AdicSheaf ℓ X} (hH : IsAdicLisseSheaf H) :
    Nonempty ((WeilSheaf.upperStar i).obj ((WeilSheaf.baseChangeField K).obj
      (WeilSheaf.geometricFiberPullback (k₀ := k) hH)) ≅
      WeilSheaf.geometricFiberPullback (k₀ := K) (IsAdicLisseSheaf.upperStar f hH)) :=
  ⟨arithmeticPullIso ((WeilSheaf.baseChangeField (X := X) K).obj
    (WeilSheaf.geometricFiberPullback (k₀ := k) hH)) hH i _ f hi (restriction K hH)⟩

end WeilII.AdicInvariantPresentation
