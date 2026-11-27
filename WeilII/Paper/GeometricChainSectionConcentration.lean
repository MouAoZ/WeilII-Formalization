module

public import WeilII.Paper.RationalLefschetzChainSection
public import WeilII.Paper.GeometricExternalTensorPowerLisse
public import WeilII.Paper.ExternalTensorPowerConstantFieldExtension
public import WeilII.Paper.WeakLefschetz
import WeilII.AlgebraicGeometry.AffineSpaceConstantExtensionGeometricCarrier
import WeilII.AlgebraicGeometry.CompactSupportGeometricCarrier
import WeilII.AlgebraicGeometry.GeometricOpenRestrictionDirectImage

open AlgebraicGeometry CategoryTheory

namespace WeilII

universe u

/-- The geometric vanishing in Zhang's Definition 2.3 gives vanishing of the
corresponding Weil cohomology over a field of definition of the hypersurface
(Zhang, pp. 2–4). The conclusion concerns each cohomology group before taking traces.

Proof. Embed the coefficient field K in the chosen algebraic closure of k. This closure
is also an algebraic closure of K. Base change takes the zero subscheme of the section
p to the zero scheme of its pullback and carries the complementary open immersion to
the new open immersion. The geometric fiber identification for constant field extension
takes the underlying sheaf of G' to the original geometric external tensor power via
the given Weil isomorphism. Adic pullback along the geometric fiber isomorphism commutes
with restriction, placement in degree zero and ordinary derived direct image for the
identified opens. Thus the underlying geometric open complex is the one appearing
in Definition 2.3. Forgetting Frobenius in compactly supported Weil cohomology computes
the compactly supported cohomology of this geometric complex: compute the direct
image with compact supports using an open compactification followed by its proper map
and use base change for the extension by zero and proper direct image. Taking
cohomology identifies the underlying vector spaces. The groups on the geometric side
are zero in degrees different from n, so the corresponding carriers are subsingletons. -/
public theorem chainSection_subsingleton_of_geometric_weakLefschetz
    {k : Type u} [Field k] [Finite k] {ℓ : ℕ} [Fact ℓ.Prime] [Fact (ringChar k ≠ ℓ)]
    (F : WeilSheaf k ℓ (affineLine k)) (hF : F.IsLisse) (n : ℕ) (hn : 2 ≤ n)
    (K : IntermediateField k (AlgebraicClosure k)) [Finite K]
    (P : MvPolynomial (Fin n) K) :
    let I := ULift.{u} (Fin n)
    let T := AlgebraicClosure k
    letI : Fact (ringChar T ≠ ℓ) := ⟨Algebra.ringChar_eq k T ▸ Fact.out⟩
    let hG := geometricExternalTensorPowerLisse F hF n hn T AlgEquiv.refl
    let S := Spec (CommRingCat.of K)
    let X := 𝔸(I; S)
    let coeff := ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ (X ↘ S).appTop).hom
    let p := MvPolynomial.eval₂Hom coeff (fun r : Fin n ↦ AffineSpace.coord S (ULift.up.{u} r)) P
    let i := X.zeroLocusSubschemeι {p}
    let b := AffineSpace.map I (Spec.map (CommRingCat.ofHom (algebraMap K T)))
    let iBar := 𝔸(I; Spec (CommRingCat.of T)).zeroLocusSubschemeι {b.appTop p}
    letI : Fact (ringChar K ≠ ℓ) := ⟨Algebra.ringChar_eq k K ▸ Fact.out⟩
    ∀ (G' : WeilSheaf K ℓ X),
      (affineSpaceWeilSheafBaseChangeField K (affineLineExternalTensorPower F hF n) ≅ G') →
      HasWeakLefschetz iBar _ hG →
      letI := isNoetherian_of_locallyOfFiniteType (X ↘ S)
      let D := openImmersionDerivedDirectImageOfRestriction i.openComplement.ι G'
      ∀ e : ℤ, e ≠ (n : ℤ) → Subsingleton (D.compactlySupportedCohomology e).carrier := by
  intro I T hG S X coeff p i b iBar G' eG hWL D e he
  have : Fact (ringChar K ≠ ℓ) := ⟨Algebra.ringChar_eq k K ▸ Fact.out⟩
  have : IsNoetherian X := isNoetherian_of_locallyOfFiniteType (X ↘ S)
  let A := Spec (.of T)
  let B := 𝔸(I; A)
  let H := affineLineExternalTensorPower F hF n
  let h := (AffineSpace.isPullback_map (n := I) (Scheme.specAlgebraicClosure k).hom).isoPullback
  obtain ⟨v, t, hv, ht, ⟨carrierIso⟩⟩ := exists_affineSpaceBaseChangeField_geometricCarrier K I H
  let U := i.openComplement
  let V := iBar.openComplement
  have basic {Y : Scheme.{u}} (s : Γ(Y, ⊤)) :
      (Y.zeroLocusSubschemeι {s}).openComplement = Y.basicOpen s := by
    apply TopologicalSpace.Opens.ext
    rw [Scheme.Hom.coe_openComplement, Y.range_zeroLocusSubschemeι_singleton, compl_compl,
      Scheme.Opens.range_ι]
  have hV : V = (v.hom ≫ (X ↘ S).geometricFiberProj) ⁻¹ᵁ U := by
    rw [hv]
    exact (basic (b.appTop p)).trans ((Scheme.preimage_basicOpen_top b p).symm.trans
      (congrArg (fun W ↦ b ⁻¹ᵁ W) (basic p).symm))
  -- Identify the open complexes before applying the derived functors.
  let model := openImmersionDerivedDirectImageOfRestriction U.ι G'
  have hD : D = model := rfl
  let pull := (ProEtale.adicUpperStar ℓ v.hom).mapDerivedCategory
  let identify := pull.mapIso (WeilComplex.forget.mapIso (eqToIso hD))
  let ej := identify ≪≫ (geometricPullback_openDirectImage U G' v V hV).some
  let forget := (WeilSheaf.objectProperty K ℓ X).ι ⋙ Endofunctor.IsoAlgebra.forget _
  let idMap := AffineSpace.map I (Spec.map
    (CommRingCat.ofHom (AlgEquiv.refl (R := k) (A₁ := T)).toRingHom))
  have hid : idMap = 𝟙 B := by
    change AffineSpace.map I (Spec.map (𝟙 (.of T))) = 𝟙 _
    rw [Spec.map_id, AffineSpace.map_id]
  let E := (ProEtale.adicUpperStar ℓ (idMap ≫ h.hom)).obj H.carrier
  have eqMap : h.hom = idMap ≫ h.hom :=
    ((congrArg (· ≫ h.hom) hid).trans (Category.id_comp h.hom)).symm
  let eSheaf : (ProEtale.adicUpperStar ℓ v.hom).obj G'.carrier ≅ E :=
    (ProEtale.adicUpperStar ℓ v.hom).mapIso (forget.mapIso eG.symm) ≪≫ carrierIso ≪≫
      (ProEtale.adicUpperStarCongr ℓ eqMap).app H.carrier
  let Hc := ProEtale.algClosedCompactlySupportedCohomology ℓ (B ↘ A) e
  let push := (ProEtale.adicLowerStar ℓ V.ι).rightDerivedFunctor
  let res := ProEtale.adicUpperStar ℓ V.ι
  let N := (ProEtale.adicUpperStar ℓ v.hom).mapDerivedCategory.obj (WeilComplex.forget.obj D)
  let L := push.obj ((DerivedCategory.singleFunctor _ 0).obj (res.obj E))
  let eOpen : N ≅ L := ej ≪≫ push.mapIso ((DerivedCategory.singleFunctor _ 0).mapIso
    (res.mapIso eSheaf))
  have hncard : Nat.card I = n := by simp [I]
  have hz : Limits.IsZero (Hc.obj L) := hWL e (by rwa [hncard])
  let M := Hc.obj N
  let transport : M ≅ Hc.obj L := Hc.mapIso eOpen
  have hzero : Limits.IsZero M := hz.of_iso transport
  let equiv := (compactSupport_linearEquiv_geometricFiber (k₀ := k) (k := ↥K) (ℓ := ℓ)
    (B ↘ A) v t ht D e).some
  have hs : Subsingleton ((WeilCoefficients.toModuleCat ℓ).obj M) :=
    ModuleCat.isZero_iff_subsingleton.mp ((WeilCoefficients.toModuleCat ℓ).map_isZero hzero)
  exact ⟨fun x y ↦ equiv.injective (@Subsingleton.elim _ hs (equiv x) (equiv y))⟩

end WeilII
