module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.DerivedComplete.Uniformizer
public import WeilConjectures.SixFunctors.ProEtale.ConstructibleSheaf
public import WeilConjectures.CategoryTheory.Sites.SheafSmul
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RestrictScalars
import WeilII.AlgebraicGeometry.ConstructibleIntegralProetaleQuotient
import WeilConjectures.AlgebraicGeometry.ProperBaseChange.WitnessCompatibility

/-!
# Étale descent of a uniformizer-power quotient

SGA 4½, *Rapport*, §§2.1, 2.5, 2.8, and the finite-ring comparison in `ConstructibleSheaf`.
-/

open AlgebraicGeometry AlgebraicGeometry.ProEtale CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace WeilII

universe u

/-- A single uniformizer-power quotient of a constructible integral module has constructible
étale origin. See SGA 4½, *Rapport*, §§2.1, 2.5, 2.8, and the finite-ring comparison in
`ConstructibleSheaf`. Put B = O/(π^(n+1)). On profinite test objects continuous functions
to B lift by a finite choice of representatives. A continuous O-valued function whose values
lie in the ideal divides continuously by its nonzero generator. Thus the quotient coefficient
sheaf is the constant finite ring B, also after inverse image to the scheme. Extension to B
on module objects is quotient by the generator, since tensoring with a module preserves
cokernels. The underlying abelian sheaf computes this cokernel. On elementary-divisor covers
of a constructible stratification the quotient is a constant finitely generated B-module.
The finite-ring comparison theorem now supplies an étale model. Restriction along O → B
commutes with comparison pullback, as can be checked on sheafifications of the underlying
abelian groups with their induced scalar maps. Transfer the quotient map across this
isomorphism. It commutes with all O-scalars, and every multiple of π^(n+1) acts by zero. -/
public theorem exists_constructibleIntegralEtaleQuotient
    (ℓ : ℕ) [Fact ℓ.Prime] {Z : Scheme.{u}} [IsNoetherian Z]
    (E : PadicAlgCl.FiniteIntermediateField ℓ) (π : PadicAlgCl.integers ℓ E.1)
    (hπ : IsLocalRing.maximalIdeal (PadicAlgCl.integers ℓ E.1) = Ideal.span {π})
    (M : Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) Z))
    (hM : IsConstructibleModuleObject _ M) (n : ℕ) :
    let I := Ideal.span {π ^ (n + 1)}
    let R := ULift.{u + 1} (PadicAlgCl.integers ℓ E.1)
    ∃ T : Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} (_ ⧸ I))),
      Scheme.IsConstructibleSheaf T ∧
      let A := (Sheaf.restrictScalars Z.smallEtaleTopology (Ideal.Quotient.mk I).ulift).obj T
      let B := (comparisonUpperStar (ModuleCat.{u + 1} R) Z).obj A
      let U := sheafCompose (Scheme.ProEt.topology Z) (forget₂ (ModuleCat.{u + 1} R) Ab)
      ∃ q : M.X ⟶ U.obj B,
        (∀ r : R, ((padicIntegersCenter Z ℓ E.1 r.down).app M).hom ≫ q =
          q ≫ U.map (Sheaf.smulEnd B r)) ∧
        (∀ x ∈ I, ((padicIntegersCenter Z ℓ E.1 x).app M).hom ≫ q = 0) ∧
        ∃ w : ((padicIntegersCenter Z ℓ E.1 (π ^ (n + 1))).app M).hom ≫ q = 0,
          Nonempty (IsColimit (CokernelCofork.ofπ q w)) := by
  classical
  let O := PadicAlgCl.integers ℓ E.1
  let I : Ideal O := Ideal.span {π ^ (n + 1)}
  let R := ULift.{u + 1} O
  let S := ULift.{u + 1} (O ⧸ I)
  let ρ : R →+* S := (Ideal.Quotient.mk I).ulift
  have hI : I = IsLocalRing.maximalIdeal O ^ (n + 1) := by
    rw [hπ, Ideal.span_singleton_pow]
  have : Finite (O ⧸ I) := hI ▸ PadicAlgCl.finite_quotient_maximalIdeal_pow ℓ E.1 (n + 1)
  have : Finite S := Finite.of_equiv (O ⧸ I) Equiv.ulift.symm
  let reduced := exists_constructibleIntegralProetaleQuotient ℓ E π hπ M hM n
  let Q := reduced.choose
  let q := reduced.choose_spec.2.choose
  have hq := reduced.choose_spec.2.choose_spec
  let lift := exists_isConstructibleSheaf_iso_comparisonUpperStar_obj S (F := Q) reduced.choose_spec.1
  let T := lift.choose
  let F := Sheaf.restrictScalars (Scheme.ProEt.topology Z) ρ
  let e := F.mapIso lift.choose_spec.2.some.symm ≪≫ (pbcComparisonRestrict Z ρ).app T
  let U := sheafCompose (Scheme.ProEt.topology Z) (forget₂ (ModuleCat.{u + 1} R) Ab)
  refine ⟨T, lift.choose_spec.1, q ≫ U.map e.hom, fun r ↦ ?_, fun x hx ↦ ?_, ?_⟩
  · have hn := congrArg U.map (Sheaf.smulEnd_comp r e.hom)
    have comm := (U.map_comp _ _).symm.trans (hn.trans (U.map_comp _ _))
    exact (Category.assoc _ q (U.map e.hom)).symm.trans <|
      (congrArg (· ≫ U.map e.hom) (hq.1 r)).trans <|
      (Category.assoc q _ _).trans <| (congrArg (q ≫ ·) comm).trans (Category.assoc q _ _).symm
  · exact (Category.assoc _ q (U.map e.hom)).symm.trans
      ((congrArg (· ≫ U.map e.hom) (hq.2.1 x hx)).trans zero_comp)
  · let w := hq.2.2.choose
    have hc := hq.2.2.choose_spec.some
    refine ⟨(Category.assoc _ q (U.map e.hom)).symm.trans
      ((congrArg (· ≫ U.map e.hom) w).trans zero_comp), ⟨?_⟩⟩
    exact IsColimit.ofIsoColimit hc (Cofork.ext (U.mapIso e) rfl)

end WeilII
