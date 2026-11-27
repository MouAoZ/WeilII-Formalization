module

public import WeilConjectures.SixFunctors.ProEtale.Adic.Constructible
public import WeilConjectures.WeilSheaf.AlgClosedCoefficientCohomology
import WeilConjectures.AlgebraicGeometry.Sites.AffineCohomologicalDimension
import WeilConjectures.CategoryTheory.Finite.FiniteMittagLeffler
import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.ConstructibleExtFinite
import WeilConjectures.AlgebraicGeometry.EtaleModuleCohomologyForget
import WeilConjectures.NumberTheory.Padics.IntegersShrinkModPow
import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.TorsionSheaf
import WeilConjectures.SixFunctors.ProEtale.Comparison.ForgetUpperStar
import WeilConjectures.SixFunctors.ProEtale.Adic.LowerStar
import WeilConjectures.ZetaFunction.SixOperations
import WeilConjectures.Topology.KrullDimension.Open
import WeilII.AlgebraicGeometry.ConstructibleAdicSheafIntegralTower
import WeilII.AlgebraicGeometry.EtaleSheafTowerVanishing
import WeilII.AlgebraicGeometry.FiniteConstructibleEtaleSheafH
import WeilII.AlgebraicGeometry.GeometricAdicOrdinaryCohomologyScalarExtension

/-!
# Affine cohomological dimension for constructible ℓ-adic sheaves

SGA 4, Exposé XIV, Théorème 3.1 gives the torsion coefficient bound. Zhang uses its
geometric ℓ-adic form after (†) on p. 2 of *On an Elementary Proof of Weil II*.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace WeilII

/-- Over the algebraic closure of a finite field, the ordinary cohomology of a constructible
`Q̄ℓ`-sheaf on an affine scheme of finite type and dimension at most `d` vanishes above `d`.
For integral `d`, the strict bound by `(d + 1).toNat` expresses this dimension hypothesis,
including the value `⊥` of the dimension of the empty scheme.

Proof. The empty scheme has zero cohomology in all degrees. Otherwise `0 ≤ d < r`.
Choose a finite coefficient field E and a constructible integral lattice M for F. For a
uniformizer π, write M as the pro-étale inverse limit of the pullbacks of its constructible
étale quotients Tₘ modulo πᵐ, for m ≥ 1. Each Tₘ is killed by a power of ℓ. Artin's affine
vanishing theorem (SGA 4, XIV, 3.1) gives Hʳ(Z, Tₘ) = 0. The groups Hʳ⁻¹(Z, Tₘ) are finite
by SGA 4½, *Théorèmes de finitude*, 1.1, applied to the structure morphism. Their images in
any fixed level stabilize, so their first derived inverse limit vanishes, also when r = d + 1.
The Milnor exact sequence for the tower of surjective quotient maps now has zero on both
sides of Hʳ(Z, M). Invert π and extend scalars from E to Q̄ℓ. Ordinary cohomology commutes
with these coefficient changes, so Hʳ(Z, F) is zero. For the integral coefficient convention
see SGA 4½, *Rapport sur la formule des traces*, §§2.1, 2.8–2.11. -/
public theorem isZero_algClosedCohomology_of_isAffine
    (k₀ : Type*) [Field k₀] [Finite k₀] (ℓ : ℕ) [Fact ℓ.Prime] [Fact (ringChar k₀ ≠ ℓ)]
    {Z : Scheme} [IsAffine Z] (a : Z ⟶ Spec (CommRingCat.of (AlgebraicClosure k₀)))
    [LocallyOfFiniteType a] (F : ProEtale.AdicSheaf ℓ Z) (hF : ProEtale.IsAdicConstructibleSheaf F)
    (d : ℤ) (hdim : topologicalKrullDim Z < ((d + 1).toNat : WithBot ℕ∞))
    (r : ℤ) (hr : d < r) :
    IsZero ((ProEtale.algClosedCohomology ℓ a r).obj
      ((DerivedCategory.singleFunctor _ 0).obj F)) := open ProEtale Opposite in by
  classical
  rcases isEmpty_or_nonempty Z with hZ | hZ
  · unfold algClosedCohomology algClosedRightDerivedGlobalSections
    exact Functor.map_isZero _ (ProEtale.isZero_of_isEmpty ℓ _)
  have hd : 0 ≤ d := by
    by_contra! hn
    have he : (d + 1).toNat = 0 := by omega
    rw [he, Nat.cast_zero] at hdim
    exact hdim.not_ge (topologicalKrullDim_nonneg (X := Z))
  obtain ⟨q, rfl⟩ : ∃ q : ℕ, r = ((q + 1 : ℕ) : ℤ) := ⟨(r - 1).toNat, by omega⟩
  have hdZ : topologicalKrullDim Z ≤ (d.toNat : WithBot ℕ∞) := by
    apply ENat.WithBot.lt_add_one_iff.mp
    have h : (d + 1).toNat = d.toNat + 1 := by omega
    simpa only [h, Nat.cast_add, Nat.cast_one] using hdim
  obtain ⟨E, π, hπ, M, hM, _, ⟨eM⟩, T, hT, t, ht, p, ⟨hp⟩, _⟩ :=
    exists_constructibleAdicSheaf_integralTower k₀ ℓ a F hF
  let O := PadicAlgCl.integers ℓ E.1
  let I (n : ℕ) : Ideal O := Ideal.span {π ^ (n + 1)}
  have hI (n : ℕ) : I n = IsLocalRing.maximalIdeal O ^ (n + 1) := by
    rw [hπ, Ideal.span_singleton_pow]
  let R := ULift.{u_1 + 1} O
  let A (n : ℕ) := ULift.{u_1 + 1} (O ⧸ I n)
  have hfinite (n : ℕ) : Finite (O ⧸ I n) := by
    rw [hI]
    infer_instance
  let levels (n : ℕ) := (Sheaf.restrictScalars Z.smallEtaleTopology
    (Ideal.Quotient.mk (I n)).ulift.{u_1 + 1, u_1 + 1}).obj (T n)
  let V := Functor.ofOpSequence (X := levels) t
  let U := sheafCompose Z.smallEtaleTopology (forget₂ (ModuleCat.{u_1 + 1} R) Ab)
  let B := V ⋙ U
  have hB (n : ℕ) : Epi (B.map (homOfLE n.le_succ).op) := by
    have : U.IsLeftAdjoint := Scheme.moduleSheafForgetIsLeftAdjoint Z R
    change Epi (U.map (V.map _))
    rw [Functor.ofOpSequence_map_homOfLE_succ]
    exact U.map_epi (t n)
  have hf (n : ℕᵒᵖ) : Finite ((Sheaf.functorH.{u_1 + 1} Z.smallEtaleTopology q).obj (B.obj n)) := by
    let j := n.unop
    have hℓ : ((ℓ ^ (j + 1) : ℕ) : A j) = 0 := by
      apply ULift.ext
      change ((ℓ ^ (j + 1) : ℕ) : O ⧸ I j) = 0
      have hmem : (ℓ : O) ^ (j + 1) ∈ I j := by
        rw [hI]
        exact Ideal.pow_mem_pow (PadicAlgCl.natCast_mem_maximalIdeal_integers ℓ E.1) _
      simpa only [Nat.cast_pow, map_pow, map_natCast] using Ideal.Quotient.eq_zero_iff_mem.mpr hmem
    have : HasInvertibleExponent (A j) (Spec (.of (AlgebraicClosure k₀))) :=
      Etale.hasInvertibleExponent_spec_algebraicClosure k₀ _ Fact.out Fact.out hℓ
    change Finite ((Sheaf.functorH.{u_1 + 1} _ q).obj
      ((sheafCompose _ (forget₂ (ModuleCat.{u_1 + 1} (A j)) Ab)).obj (T j)))
    exact finite_functorH_constructible_etale (A j) a (T j) q
  have hz (n : ℕᵒᵖ) :
      IsZero ((Sheaf.functorH.{u_1 + 1} Z.smallEtaleTopology (q + 1)).obj (B.obj n)) := by
    let j := n.unop
    apply AddCommGrpCat.isZero_iff_subsingleton.mpr
    apply Scheme.subsingleton_H_of_lt_of_isAffine_of_isSepClosed d.toNat a hdZ
      ((sheafCompose _ (forget₂ (ModuleCat.{u_1 + 1} (A j)) Ab)).obj (T j))
      ((Scheme.isTorsionModuleSheaf_iff_isTorsion (T j)).1 inferInstance)
    omega
  have hlim := isZero_functorH_limit_etaleTower Z q B hB hf hz
  let eTower := Functor.isoWhiskerLeft V (sheafComposeForget₂CompComparisonUpperStarIso R Z)
  let eLim := hp.conePointUniqueUpToIso (limit.isLimit _) ≪≫ (lim.mapIso eTower).symm
  have hAb := hlim.of_iso ((Sheaf.functorH.{u_1 + 1} _ (q + 1)).mapIso eLim)
  have hInt : IsZero ((integralProEtaleCohomology Z ℓ E (q + 1)).obj M) :=
    ModuleCat.isZero_iff_subsingleton.mpr (AddCommGrpCat.isZero_iff_subsingleton.mp hAb)
  obtain ⟨e⟩ := nonempty_integralProEtaleCohomology_extendScalars_iso k₀ ℓ a E (q + 1)
  let equiv := adicSheafEquivCondensedMod ℓ Z
  let eF := equiv.inverse.mapIso eM ≪≫ equiv.unitIso.symm.app F
  let H := DerivedCategory.singleFunctor _ 0 ⋙ algClosedCohomology ℓ a (q + 1 : ℕ)
  exact ((ModuleCat.extendScalars (PadicAlgCl.integersToULift ℓ E.1)).map_isZero hInt).of_iso
    ((H.mapIso eF).symm ≪≫ (e.app ⟨M, hM⟩).symm)

end WeilII
