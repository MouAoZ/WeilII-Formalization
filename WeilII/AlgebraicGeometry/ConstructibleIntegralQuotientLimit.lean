module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.DerivedComplete.Constructible
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.DerivedComplete.LiftMorphisms
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.IntegralReductionTriangleNatural
import WeilConjectures.AlgebraicGeometry.ProEtale.RepleteAb
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.RegularEndDerived
import WeilII.CategoryTheory.CompleteQuotientTower

/-!
# The ordinary limit of the uniformizer quotients

SGA 4½, *Rapport*, §§2.1, 2.8, and the derived reduction tower in `DerivedComplete.LiftMorphisms`.
-/

open AlgebraicGeometry AlgebraicGeometry.ProEtale CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj

namespace WeilII

universe u

/-- The quotient cone of a torsion-free constructible integral sheaf is an ordinary limit.
See SGA 4½, *Rapport*, §§2.1, 2.8 and the canonical reduction tower in
`DerivedComplete.LiftMorphisms`. Place M in degree zero. It is bounded constructible, hence
derived complete. If e is the ramification index, (ℓ^i) = (π^(e*i)). The canonical reduction
triangle for ℓ^i has vanishing negative cohomology by injectivity and has zero-th cohomology
the cokernel of ℓ^i. The reduction unit gives its quotient projection. The homotopy limit
theorem thus applies to the tower of ordinary module quotients at exponents e*i, i ≥ 1.
For any module sheaf W apply Hom(W[0],−) to its product triangle. Hom commutes with products
and Hom(W[0],Q[−1]) vanishes for every degree-zero quotient. Exactness identifies Hom(W,M)
via the projections with the kernel of one minus the shift on the product of Hom groups,
precisely the compatible families. The forgetful functor preserves limits and computes
cokernels. The given cokernel projections therefore identify uniquely with the underlying
module quotient projections. Since those projections are epimorphisms, compatibility forces
all transition maps under the identifications. Finally each positive exponent is bounded
above by a multiple of e. Projecting down from such a multiple uniquely extends a compatible
family on this cofinal subtower. -/
public theorem isLimit_constructibleIntegralQuotientCone
    (ℓ : ℕ) [Fact ℓ.Prime] {Z : Scheme.{u}} [IsNoetherian Z]
    (E : PadicAlgCl.FiniteIntermediateField ℓ) (π : PadicAlgCl.integers ℓ E.1)
    (hπ : IsLocalRing.maximalIdeal (PadicAlgCl.integers ℓ E.1) = Ideal.span {π})
    (M : Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) Z))
    (hM : IsConstructibleModuleObject _ M) (hm : Mono ((padicIntegersCenter Z ℓ E.1 π).app M))
    {D : ℕᵒᵖ ⥤ Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}}
    (p : (Functor.const ℕᵒᵖ).obj M.X ⟶ D)
    (hq : ∀ n : ℕ, ∃ w : ((padicIntegersCenter Z ℓ E.1 (π ^ (n + 1))).app M).hom ≫
        p.app (op n) = 0, Nonempty (IsColimit (CokernelCofork.ofπ (p.app (op n)) w))) :
    Nonempty (IsLimit (Cone.mk M.X p)) := by
  let z := (padicIntegersCenter Z ℓ E.1 π).app M
  let U := Mod.forget (D := Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
    (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) Z)
  let e : End M.X := .of z.hom
  have : Mono e.asHom := U.map_mono z
  have : IsIso (𝟙 _ - powShift z) :=
    isIso_sub_powShift_padicIntegersCenter_of_isConstructible
      (hπ ▸ Ideal.mem_span_singleton_self π) M hM
  have : IsIso (𝟙 _ - powShift e.asHom) := (isIso_map_sub_powShift_iff U z).mp (U.map_isIso _)
  have hpow (n : ℕ) : ((padicIntegersCenter Z ℓ E.1 (π ^ (n + 1))).app M).hom =
      (e ^ (n + 1)).asHom := by
    induction n with
    | zero => simp [e, z]
    | succ n ih =>
      rw [pow_succ' π (n + 1), pow_succ e (n + 1), End.mul_asHom, ← ih]
      simp only [e, z, padicIntegersCenter, padicIntegersRegularEndOfAlgebra_mul]
      have hcomm : IsCommMonObj (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) Z) :=
        isCommMonObj_condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) Z
      exact U.congr_map (@Mod.regularEndSMul_comp _ _ _ _ _ _ _ _ _ hcomm
        (padicIntegersRegularEndOfAlgebra Z ℓ E.1 π)
        (padicIntegersRegularEndOfAlgebra Z ℓ E.1 (π ^ (n + 1))) M)
  have hepi (n : ℕ) : Epi (p.app (op n)) := epi_of_isColimit_cofork (hq n).choose_spec.some
  apply isLimit_quotientCone_of_isIso_sub_powShift e p
  · intro n
    rw [← hpow n]
    exact hq n
  · let := Abelian.hasFiniteBiproducts (C := Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
    exact epi_pi_map_of_epi_π_app_zero Scheme.ProEt.epi_π_app_zero_of_epi_ab _

end WeilII
