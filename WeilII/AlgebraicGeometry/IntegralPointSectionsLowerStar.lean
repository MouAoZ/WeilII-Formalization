module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.EtaleOrigin.Constructible.Regular
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UniformizerReduction
public import WeilConjectures.TraceFormula.PointFiberFunctorIntegral
public import WeilConjectures.CategoryTheory.ModuleObjects.SectionAction
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ResidueFieldModuleSheafEquivalenceUpperLowerStar
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ResidueFieldTransportSection

/-!
# Integral point sections of an ordinary pro-étale direct image

This comparison combines evaluation at the unit in `regularHomEquivSections` with the
terminal-object identification `overPullbackObjMkIdIso` from weil-conjectures.
-/

open AlgebraicGeometry AlgebraicGeometry.ProEtale CategoryTheory Opposite
open scoped CategoryTheory.Obj

namespace WeilII

universe u

/-- For any morphism to a field spectrum, integral point sections of the ordinary direct image
are naturally isomorphic as abelian groups to terminal sections of the underlying sheaf.
The first formula evaluates each component at the unit. The second identifies multiplication
by an integral scalar with the action of its constant section on the original module.

Proof. Write P for the direct image of N. A point section is a module map from the regular
module to P. Evaluation at the unit, followed by evaluation on the terminal site object of
the field spectrum, is the composite of `Mod.regularHomAddEquiv` and
`Sheaf.unitHomEvalAddEquiv`. Its inverse takes the map from the unit sheaf corresponding to
a section and extends it by the regular module action. The underlying sheaf of P is the
ordinary direct image of the underlying sheaf of N. Its terminal sections are thus sections
on the pullback of the terminal object. Restrict along the inverse of
`overPullbackObjMkIdIso a` to obtain a section on Z. Restriction along the forward map is
the inverse by functoriality. Evaluation commutes with postcomposition by
`regularHomEquivSections_comp`, and restriction commutes with every sheaf morphism by
naturality. This gives the asserted natural isomorphism.

Write c for the element of the ring of integers corresponding to r. In `pointSectionsIntegral`,
r acts by precomposition with multiplication by the pullback of the condensed constant c.
The induced metric on the coefficient field is ultrametric, so its ring of integers is
Hausdorff and totally disconnected. Thus `continuousMapCoefficientSectionRingHom_const_hom`
identifies that pullback with the section of the constant function c. By
`Mod.one_comp_regularLift_comp_hom` and `Sheaf.unitHomEval_comp`, evaluation sends
precomposition to the action of this section on P. By
`sectionActRingHom_lowerStar_continuousMapCoefficientSectionRingHom`, that action is the
direct image of the action on N of the composite constant function, which again has value c.
Naturality of this sheaf endomorphism with respect to the terminal-object isomorphism gives
the scalar formula after restriction. -/
public theorem exists_integralPointSectionsLowerStarIso
    (k : Type u) [Field k] (Z : Scheme.{u}) (a : Z ⟶ Spec (.of k))
    (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ) :
    letI := PadicAlgCl.normedFieldOfAlgebra ℓ E.1
    let Λ := Profinite.padicIntegersRingObj.{u} ℓ E.1
    let O := Shrink.{u + 1} (PadicAlgCl.integers ℓ E.1)
    let push := CondensedRing.lowerStar Λ a
    let S := CondensedRing.pointSectionsIntegral ℓ k E
    let ΓZ := (sheafSections (Scheme.ProEt.topology Z) Ab.{u + 1}).obj
      (op (Scheme.ProEt.mk (𝟙 Z)))
    ∃ e : push ⋙ S ⋙ forget₂ (ModuleCat.{u + 1} O) Ab ≅ Mod.forget (condensedRingObj Λ Z) ⋙ ΓZ,
      (∀ N (φ : S.obj (push.obj N)), e.hom.app N φ =
        N.X.obj.map (Iso.inv (C := Z.ProEt) (overPullbackObjMkIdIso a)).op
          (regularHomEquivSections (PadicAlgCl.integers ℓ E.1) _ (push.obj N) φ)) ∧
      ∀ N (r : O) (φ : S.obj (push.obj N)),
        let c := (PadicAlgCl.shrinkRingEquiv ℓ E.1).symm r
        let μ := Mod.sectionActRingHom N (padicIntegersConstSectionRingHom ℓ E Z c)
        e.hom.app N (r • φ) = (ΓZ.map μ.asHom) (e.hom.app N φ) := by
  intro Λ O push S ΓZ
  let := PadicAlgCl.normedFieldOfAlgebra ℓ E.1
  let R := ↥(PadicAlgCl.integers ℓ E.1)
  have : IsTopologicalRing R := PadicAlgCl.isTopologicalRing_integers ℓ E.1
  let s := Spec (.of k)
  let t := Iso.symm (C := Z.ProEt) (overPullbackObjMkIdIso a)
  let restriction := Iso.hom (C := Z.ProEt) t
  let Ts := Scheme.ProEt.mk (𝟙 s)
  let F := push ⋙ S ⋙ forget₂ (ModuleCat.{u + 1} O) Ab
  let G := Mod.forget (condensedRingObj Λ Z) ⋙ ΓZ

  let component (N) : F.obj N ≅ G.obj N :=
    (AddEquiv.toAddCommGrpIso (X := F.obj N) (Y := (push.obj N).X.obj.obj (op Ts))
      ((Mod.regularHomAddEquiv (push.obj N)).trans
        (Sheaf.unitHomEvalAddEquiv (Scheme.ProEt.isTerminalMkId s) (push.obj N).X))) ≪≫
      N.X.obj.mapIso (Iso.op (C := Z.ProEt) t)
  have natural {N M} (h : N ⟶ M) :
      F.map h ≫ (component M).hom = (component N).hom ≫ G.map h := by
    ext φ
    exact (h.hom.hom.naturality_apply restriction.op (regularHomEquivSections R s _ φ)).symm
  let e : F ≅ G := NatIso.ofComponents component natural
  refine ⟨e, fun _ _ ↦ rfl, ?_⟩

  intro N r φ
  let c := (PadicAlgCl.shrinkRingEquiv ℓ E.1).symm r
  let σ := MonObj.Γ.mapFunctor (upperStarFromPoint s)
    (CondensedRing.padicIntegersConstRingHom ℓ E c)
  let P := push.obj N
  let μ := (Mod.sectionActRingHom N (padicIntegersConstSectionRingHom ℓ E Z c)).asHom
  have := PadicAlgCl.isUltrametricDist_ofAlgebra ℓ E.1
  have : T2Space R :=
    inferInstanceAs (T2Space {y : E.1 // y ∈ PadicAlgCl.integers ℓ E.1})
  have : TotallyDisconnectedSpace R :=
    inferInstanceAs (TotallyDisconnectedSpace {y : E.1 // y ∈ PadicAlgCl.integers ℓ E.1})
  have hσ : (continuousMapCoefficientSectionRingHom s R (ContinuousMap.const s c)).hom =
      σ.hom := continuousMapCoefficientSectionRingHom_const_hom s R c
  have hμ : Mod.globalSmul σ.hom P = (lowerStar Ab a).map μ := by
    rw [← hσ]
    exact @sectionActRingHom_lowerStar_continuousMapCoefficientSectionRingHom
      R (inferInstance : TopologicalSpace R) _ ‹IsTopologicalRing _› ‹T2Space _›
      ‹TotallyDisconnectedSpace _› s Z a N (ContinuousMap.const s c)

  let x : Mod.regular (condensedRingObj Λ s) ⟶ P := φ
  have eval : regularHomEquivSections R s P (r • φ) =
      ((lowerStar Ab a).map μ).hom.app (op Ts) (regularHomEquivSections R s P φ) := by
    refine (congrArg (Sheaf.unitHomEval (J := Scheme.ProEt.topology s) Ts)
      (Mod.one_comp_regularLift_comp_hom σ.hom x)).trans ?_
    exact congrArg (fun g : P.X ⟶ P.X ↦ g.hom.app (op Ts)
      (regularHomEquivSections R s P φ)) hμ
  change N.X.obj.map restriction.op (regularHomEquivSections R s P (r • φ)) =
    μ.hom.app _ (N.X.obj.map restriction.op (regularHomEquivSections R s P φ))
  rw [eval]
  exact (μ.hom.naturality_apply restriction.op _).symm

end WeilII
