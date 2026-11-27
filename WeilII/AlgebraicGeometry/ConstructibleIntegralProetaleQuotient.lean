module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.DerivedComplete.Uniformizer
public import WeilConjectures.SixFunctors.ProEtale.ConstructibleSheaf
public import WeilConjectures.CategoryTheory.Sites.SheafSmul
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RestrictScalars
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.IntegralLisseLocalStructure

import WeilII.AlgebraicGeometry.CondensedPrincipalQuotient
import WeilConjectures.NumberTheory.Padics.IntegersShrinkModPow
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.ExtendScalarsConstructible
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.EtaleOrigin.Constructible
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.Scalars

/-!
# Finite discrete coefficients of an integral quotient

SGA 4½, *Rapport*, §§2.1, 2.5, 2.8.
-/

open AlgebraicGeometry AlgebraicGeometry.ProEtale CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace WeilII

universe u

/-- The quotient by a positive uniformizer power is a constructible pro-étale sheaf over
the discrete quotient ring. See SGA 4½, *Rapport*, §§2.1, 2.5, 2.8. The ring
B = O/(π^(n+1)) is finite since (π) is the maximal ideal of a finite extension.
Each continuous B-valued function on a profinite set lifts along a finite choice of
representatives; if an O-valued function is zero modulo π^(n+1), divide its values
continuously by π^(n+1). This identifies the quotient of the continuous coefficient sheaf
with the discrete constant ring B, and the identification pulls back to the scheme.
Tensor the coefficient cokernel with M. Extension to the quotient ring is thus the
cokernel of multiplication by π^(n+1), computed on underlying abelian sheaves.
Modules over a discrete constant ring are sheaves valued in modules over that ring.
On an elementary-divisor cover of each stratum, tensoring gives a finite sum of constant
cyclic B-modules and copies of B, hence a finite locally constant module. The quotient
projection is O-linear and every element of the kernel ideal acts as zero. -/
public theorem exists_constructibleIntegralProetaleQuotient
    (ℓ : ℕ) [Fact ℓ.Prime] {Z : Scheme.{u}} [IsNoetherian Z]
    (E : PadicAlgCl.FiniteIntermediateField ℓ) (π : PadicAlgCl.integers ℓ E.1)
    (hπ : IsLocalRing.maximalIdeal (PadicAlgCl.integers ℓ E.1) = Ideal.span {π})
    (M : Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) Z))
    (hM : IsConstructibleModuleObject _ M) (n : ℕ) :
    let I := Ideal.span {π ^ (n + 1)}
    let R := ULift.{u + 1} (PadicAlgCl.integers ℓ E.1)
    ∃ Q : Sheaf (Scheme.ProEt.topology Z) (ModuleCat.{u + 1} (ULift.{u + 1} (_ ⧸ I))),
      ProEtale.IsConstructible _ Q ∧
      let B := (Sheaf.restrictScalars (Scheme.ProEt.topology Z) (Ideal.Quotient.mk I).ulift).obj Q
      let U := sheafCompose (Scheme.ProEt.topology Z) (forget₂ (ModuleCat.{u + 1} R) Ab)
      ∃ q : M.X ⟶ U.obj B,
        (∀ r : R, ((padicIntegersCenter Z ℓ E.1 r.down).app M).hom ≫ q =
          q ≫ U.map (Sheaf.smulEnd B r)) ∧
        (∀ x ∈ I, ((padicIntegersCenter Z ℓ E.1 x).app M).hom ≫ q = 0) ∧
        ∃ w : ((padicIntegersCenter Z ℓ E.1 (π ^ (n + 1))).app M).hom ≫ q = 0,
          Nonempty (IsColimit (CokernelCofork.ofπ q w)) := by
  classical
  let K : Type := E.1
  let nf := PadicAlgCl.normedFieldOfAlgebra ℓ K
  let : TopologicalSpace K := nf.toUniformSpace.toTopologicalSpace
  let O : Type := PadicAlgCl.integers ℓ K
  let : TopologicalSpace O := TopologicalSpace.induced (fun x : O ↦ (x : K)) inferInstance
  have : IsTopologicalRing O := inferInstanceAs (IsTopologicalRing (PadicAlgCl.integers ℓ K))
  let a : O := π ^ (n + 1)
  let I : Ideal O := Ideal.span {a}
  let B := O ⧸ I
  let ρ : O →+* B := Ideal.Quotient.mk I
  let : TopologicalSpace B := ⊥
  have : DiscreteTopology B := ⟨rfl⟩
  have : IsTopologicalRing B := DiscreteTopology.topologicalRing
  have hI : I = IsLocalRing.maximalIdeal O ^ (n + 1) := by
    rw [hπ, Ideal.span_singleton_pow]
  have : Finite B := show Finite (O ⧸ I) from
    hI ▸ PadicAlgCl.finite_quotient_maximalIdeal_pow ℓ K (n + 1)
  -- Reduction to B factors through the continuous discrete reduction modulo ℓ^(n+1).
  have hdvd : π ∣ (ℓ : O) := Ideal.mem_span_singleton.mp
    (hπ ▸ PadicAlgCl.natCast_mem_maximalIdeal_integers ℓ E.1)
  have hle : Ideal.span {(ℓ : O) ^ (n + 1)} ≤ I :=
    Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow_of_dvd hdvd _)
  let factor : PadicAlgCl.integersModPow ℓ K (n + 1) → B := Ideal.Quotient.factor hle
  have hc : Continuous ρ := (show Continuous factor from continuous_of_discreteTopology).comp
    (PadicAlgCl.continuous_integersModPowMk ℓ K (n + 1))
  have hπ0 : π ≠ 0 := fun h ↦ PadicAlgCl.maximalIdeal_integers_ne_bot ℓ E.1 (by
    rw [hπ, h, Ideal.span_singleton_zero])
  have ha0 : (a : K) ≠ 0 := fun h ↦ pow_ne_zero (n + 1) hπ0 (Subtype.ext h)
  have he : Topology.IsEmbedding (a * · : O → O) :=
    (Topology.IsEmbedding.of_comp_iff Topology.IsEmbedding.subtypeVal).mp
      ((Homeomorph.mulLeft₀ (a : K) ha0).isEmbedding.comp Topology.IsEmbedding.subtypeVal)
  let v : Profinite.padicIntegersRingObj.{u} ℓ K ⟶ Profinite.continuousMapRingObj B :=
    Profinite.continuousMapRingObjMap ρ hc
  have : IsMonHom v := inferInstanceAs (IsMonHom (Profinite.continuousMapRingObjMap.{u} ρ hc))
  let φ := coefficientMap v Z
  let : BraidedCategory (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) :=
    (Sheaf.symmetricCategory _ _).toBraidedCategory
  have : IsCommMonObj (condensedRingObj (Profinite.padicIntegersRingObj ℓ K) Z) :=
    isCommMonObj_condensedRingObj _ Z
  have : IsCommMonObj (condensedRingObj (Profinite.continuousMapRingObj B) Z) :=
    isCommMonObj_condensedRingObj _ Z
  have kills (x : O) (hx : x ∈ I) :
      (padicIntegersRegularEndOfAlgebra Z ℓ K x).hom ≫ φ = 0 := by
    have hcond : Profinite.padicIntegersRingObjMulLeft.{u} ℓ K x ≫ v = 0 := by
      ext V y
      refine congrArg ULift.up (ContinuousMap.ext fun t ↦ ?_)
      change ρ (x * y.down t) = 0
      rw [map_mul, show ρ x = 0 from Ideal.Quotient.eq_zero_iff_mem.mpr hx, zero_mul]
    rw [padicIntegersRegularEnd_hom]
    exact ((upperStarFromPoint Z).map_comp _ _).symm.trans
      ((congrArg (upperStarFromPoint Z).map hcond).trans ((upperStarFromPoint Z).map_zero _ _))
  have hcoef := shortExact_condensedPrincipalQuotient.{u} (R := O) (B := B) a ρ hc
    Ideal.Quotient.mk_surjective (Ideal.mk_ker (I := I)) he
  let N := (Mod.extendScalars φ).obj M
  let Q := (finiteCoefficientModEquivalence Z B).functor.obj N
  have hQ : ProEtale.IsConstructible _ Q :=
    isConstructible_finiteCoefficientModEquivalence_functor_obj B
      (CondensedRing.IsConstructibleModuleObject.extendScalars v hM)
  let D := (Sheaf.restrictScalars (Scheme.ProEt.topology Z) ρ.ulift).obj Q
  let U := sheafCompose (Scheme.ProEt.topology Z)
    (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} O)) Ab)
  let q := Mod.extendUnit φ M
  let πQ : M.X ⟶ U.obj D := q.hom
  have lin (r : ULift.{u + 1} O) : ((padicIntegersCenter Z ℓ E.1 r.down).app M).hom ≫ πQ =
      πQ ≫ U.map (Sheaf.smulEnd D r) := by
    have hn := congrArg Mod.Hom.hom ((padicIntegersCenter Z ℓ E.1 r.down).naturality q)
    refine hn.symm.trans (congrArg (q.hom ≫ ·) ?_)
    refine (regularEndSMul_padicIntegersRegularEnd_hom Z ℓ K r.down
      ((Mod.comap φ).obj N)).trans ?_
    rw [Mod.globalSmul_comap]
    change Mod.globalSmul (padicIntegersConstSection Z ℓ E.1 r.down ≫
      (upperStarFromPoint Z).map v) N = _
    rw [padicIntegersConstSection, Category.assoc, ← Functor.map_comp,
      Profinite.continuousMapConstRingHom_hom_comp_continuousMapRingObjMap]
    ext V y
    exact (finiteCoefficientModEquivalence_smul Z B N V (ρ r.down) y).symm
  refine ⟨Q, hQ, πQ, lin, ?_, ?_⟩
  · intro x hx
    exact congrArg Mod.Hom.hom
      (Mod.regularEndSMul_comp_extendUnit (φ := φ)
        (r := padicIntegersRegularEndOfAlgebra Z ℓ K x) (kills x hx) M)
  · let w := hcoef.choose
    have hcoeff := hcoef.choose_spec
    let F := upperStarFromPoint Z
    have adj := pointUpperStarLowerStarAdjunction.comp
      (ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} (toSpecZ Z))
    have : PreservesColimitsOfSize.{0, 0} F := adj.leftAdjoint_preservesColimits
    let r := padicIntegersRegularEndOfAlgebra Z ℓ K a
    have hr : r.hom = F.map (Profinite.continuousMapRingObjMulLeft O a) :=
      padicIntegersRegularEnd_hom Z ℓ E.1 a
    have w' : r.hom ≫ φ = 0 := kills a (Ideal.mem_span_singleton_self a)
    have h' : (ShortComplex.mk _ _ w').ShortExact :=
      ShortComplex.shortExact_of_iso
        (ShortComplex.isoMk (S₁ := (ShortComplex.mk _ _ w).map F)
          (Iso.refl _) (Iso.refl _) (Iso.refl _)
          ((Category.id_comp r.hom).trans (hr.trans (Category.comp_id _).symm))
          ((Category.id_comp φ).trans (Category.comp_id φ).symm))
        (hcoeff.map_of_exact F)
    have hu := Mod.exact_regularEndSMul_extendUnit (φ := φ) (r := r) w' h' M
    have hepi := hu.2
    let forgetM := Mod.forget (D := Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ K) Z)
    have wq := Mod.regularEndSMul_comp_extendUnit (φ := φ) (r := r) w' M
    refine ⟨congrArg Mod.Hom.hom wq, ⟨?_⟩⟩
    exact isColimitCoforkMapOfIsColimit' forgetM wq hu.1.gIsCokernel

end WeilII
