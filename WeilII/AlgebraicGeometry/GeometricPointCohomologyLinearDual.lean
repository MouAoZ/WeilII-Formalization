module

public import Mathlib.LinearAlgebra.Dual.Defs
public import WeilConjectures.SixFunctors.ProEtale.Adic.CondensedModelDerived
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleLowerStar
public import WeilConjectures.TraceFormula.Basic
import WeilII.HomologicalAlgebra.DerivedRegularFiberDuality
import WeilII.HomologicalAlgebra.GradedFiberDuality
import WeilII.AlgebraicGeometry.PointFiberNativeSections
import WeilII.AlgebraicGeometry.BoundedConstructibleHomShift
import WeilConjectures.Algebra.Homology.DerivedCategory.HomToInjective
import WeilConjectures.CategoryTheory.DerivedCategory.HomSingleProjective
import WeilConjectures.TraceFormula.DualizableShift
import WeilConjectures.TraceFormula.PointFiberFunctor

/-!
# Cohomology of the internal dual on a geometric point

SGA 4, XVIII, 3.2.6.1–3.2.6.2 identifies the cohomology of the derived dual using
self-injectivity of the coefficients. Here the coefficients form the field `ℚ̄_ℓ` and
cohomology is taken by the native adic derived global sections functor. Katz, Appendix
A.5–A.6, pp. 220–221, uses this duality after taking global sections.
-/

open AlgebraicGeometry CategoryTheory MonoidalCategory Opposite
open AlgebraicGeometry.ProEtale.CondensedRing
open scoped CategoryTheory.Obj

namespace WeilII

universe u

/-- For a bounded constructible complex on the geometric point of a finite field, the linear
dual of its degree-`r` cohomology is naturally its internal dual's degree-`-r` cohomology.

Proof (SGA 4, XVIII, 3.2.6.1–3.2.6.2, with the point evaluation of
`WeilConjectures.TraceFormula.PointFiberFunctor`). Write `U` for the tensor unit, `D Q` for
`RHom(Q,U)`, and `B` for the condensed point fiber. Full faithfulness of `B` and its unit
isomorphism `B U ≅ R[0]`, where `R` is the lifted coefficient field, identify `Hom(U,T)`
with `Hom(R[0],B T)`. Since the free module `R` is projective, taking degree-zero cohomology
and evaluating at one identify the latter group with `H⁰(B T)`. Likewise `Hom(Q,U)` identifies
with `Hom(B Q,R[0])`. Every functional on a subspace extends by zero on a complement, so
`R` is injective and taking degree-zero cohomology identifies this group with `H⁰(B Q)ᵛ`.

Uncurrying followed by the inverse right unitor identifies `Hom(U,D Q)` with `Hom(Q,U)`.
This bijection is additive by additivity of tensor and composition. For a scalar `a`, lift
multiplication by `a` through the fully faithful fiber to an endomorphism `m` of `U`.
Precomposition by `m` on the first Hom group corresponds by adjunction to precomposition
on `Q` by the endomorphism induced by `Q ⊗ m` via the right unitor. This endomorphism is
natural in `Q` and at `U` it equals `m`, by the unit identities. Thus its effect on a map
`Q ⟶ U` is postcomposition by `m`. Both actions become multiplication by `a` under the
cohomology identifications. The composite is therefore a linear equivalence from `H⁰(B(D Q))`
to `H⁰(B Q)ᵛ`. It is contravariantly natural by functoriality of cohomology and naturality
of the tensor–Hom adjunction in its parameter.

Apply this comparison to `Q = P[r]`. For every test object `T`, the tensor shift isomorphisms
identify `P[r] ⊗ T` with `P ⊗ T[r]`. Adjunction in each case and inverse shifts thus identify
`Hom(T,D(P[r]))` with `Hom(T,(D P)[-r])`, naturally in both variables. Yoneda gives the
corresponding natural isomorphism of internal duals. The fiber commutes with shifts and
`H⁰(L[t]) ≅ Hᵗ(L)`. Transport along the coefficient-linear natural comparison between the
fiber and native derived sections, restrict scalars along the lift of the coefficient field,
and apply `ULift.down` to functional values. Inverting the resulting equivalence gives the
stated family. On a morphism the dual actions are precomposition, as in the displayed square. -/
public theorem exists_natural_geometricPointCohomologyLinearDual
    (k₀ : Type u) [Field k₀] [Finite k₀] (ℓ : ℕ) [Fact ℓ.Prime] [Fact (ringChar k₀ ≠ ℓ)]
    (r : ℤ) :
    let k := AlgebraicClosure k₀
    have : Fact (ringChar k).Prime := ⟨Algebra.ringChar_eq k₀ k ▸ CharP.prime_ringChar k₀⟩
    have : Fact (ringChar k ≠ ℓ) := ⟨Algebra.ringChar_eq k₀ k ▸ (Fact.out : ringChar k₀ ≠ ℓ)⟩
    let s := point k
    let F := (ProEtale.boundedConstructible
      (ProEtale.condensedRingObj (Profinite.padicAlgClRingObj ℓ) s.left)).ι ⋙
      (ProEtale.adicSheafDerivedEquivCondensedMod ℓ s.left).inverse ⋙
      (ProEtale.adicGlobalSections ℓ s.left).rightDerivedFunctor
    let H := fun i ↦ F ⋙ DerivedCategory.homologyFunctor _ i ⋙ WeilCoefficients.toModuleCat ℓ
    let U : Dᵇc(s.left)⟦Profinite.padicAlgClRingObj ℓ⟧ :=
      ⟨_, boundedConstructible_tensorUnit _ s.left⟩
    let D := (boundedConstructibleHom ℓ s).flip.obj U
    ∃ e : ∀ P, Module.Dual (PadicAlgCl ℓ) ((H r).obj P) ≃ₗ[PadicAlgCl ℓ]
        (H (-r)).obj (D.obj (op P)),
      ∀ {P P'} (f : P ⟶ P') (φ : Module.Dual (PadicAlgCl ℓ) ((H r).obj P')),
        e P (φ.comp ((H r).map f).hom) = (H (-r)).map (D.map f.op) (e P' φ) := by
  classical
  intro k hchar hℓ s F H U D
  let B := pointFiberFunctor ℓ k
  obtain ⟨eF⟩ := nonempty_pointFiberFunctorIsoAdicRightDerivedGlobalSections ℓ k
  obtain ⟨bff⟩ := (Functor.FullyFaithful.nonempty_iff_map_bijective B).2
    (bijective_pointFiberFunctor_map ℓ k)
  let ff : F.FullyFaithful := bff.ofIso eF
  let R := ULift.{u + 1} (PadicAlgCl ℓ)
  let reg := ModuleCat.of R R
  let single := DerivedCategory.singleFunctor (WeilCoefficients ℓ) 0
  let h0 := DerivedCategory.homologyFunctor (WeilCoefficients ℓ) 0
  let res := WeilCoefficients.toModuleCat ℓ
  let eu : F.obj U ≅ single.obj reg := eF.symm.app U ≪≫ pointFiberFunctorUnitIso ℓ k
  let adj := boundedConstructibleTensorHomAdjunction₂ (X := s) ℓ
  have tensorAdd (Q : Dᵇc(s.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
      ((boundedConstructibleTensor ℓ s).obj Q).Additive := by
    have := (adj.adj Q).leftAdjoint_preservesColimits
    exact rightExactFunctor_le_additiveFunctor _ _ ((boundedConstructibleTensor ℓ s).obj Q)
      (by rw [rightExactFunctor_iff]; infer_instance)
  have : F.Additive := Functor.additive_of_iso eF
  obtain ⟨z, hz⟩ := @exists_natural_derivedRegularFiberDual _ _ _ _ _
    (ULift.ringEquiv (R := PadicAlgCl ℓ)).symm _ _ _ _ _ adj tensorAdd F _ ff eu
  let : F.CommShift ℤ := Functor.CommShift.ofIso eF ℤ
  let shiftH (n : ℤ) : shiftFunctor _ n ⋙ H 0 ≅ H n :=
    Functor.isoWhiskerRight (F.commShiftIso n) (h0 ⋙ res) ≪≫
      Functor.isoWhiskerLeft F (Functor.isoWhiskerRight
        (h0.shiftIso n 0 n (by omega)) res)
  let ds : (shiftFunctor _ r).op ⋙ D ≅ D ⋙ shiftFunctor _ (-r) :=
    (nonempty_boundedConstructibleHomSourceShiftIso ℓ s U r).some
  exact exists_natural_gradedDual_of_zero D H r shiftH ds z hz

end WeilII
