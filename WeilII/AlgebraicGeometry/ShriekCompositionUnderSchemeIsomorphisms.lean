module

public import WeilConjectures.TraceFormula.ExceptionalKunnethFunctoriality
public import WeilConjectures.WeilSheaf.SmoothPurityFieldPastedProper
public import WeilConjectures.WeilSheaf.SmoothPurityPointOpenComparison
public import WeilII.AlgebraicGeometry.OpenExtensionExchangeUnit
import WeilII.AlgebraicGeometry.ShriekCompositionFieldStructures
import WeilII.AlgebraicGeometry.ShriekBaseChangeChangePrimedStructure
meta import WeilConjectures.Tactic.ExactByKernel

/-!
# Transport of lower-shriek composition along scheme isomorphisms

Zhang's deduction of Theorem 1.1 from Proposition 1.5 uses the Frobenius-equivariant Künneth
map. Its lower-shriek composition factor uses the vertical pasting formula of
`WeilConjectures.TraceFormula.ExceptionalKunnethFunctoriality` along underlying scheme
isomorphisms.
-/

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.ProEtale AlgebraicGeometry.ProEtale.CondensedRing
open scoped CategoryTheory.Obj

namespace WeilII

universe u

/-- Exchanging the composite lower shriek across the scheme isomorphisms and expanding the
primed composite agrees with expanding the unprimed composite and exchanging each factor.
The two pullback witnesses follow from the commuting faces by `IsPullback.of_horiz_isIso`.
The composite witness defaults to their vertical paste.

Proof (weil-conjectures revision `497f33d`, `ExceptionalKunnethFunctoriality.lean`,
`SmoothPurityFieldPastedExchange.lean` and `LowerShriek/CompositionTriangle.lean`).
Give each primed scheme the structure map obtained by composing its isomorphism with the
unprimed structure map. These schemes are still separated and of finite type. The two
commutativities put the primed arrows in this slice. Both squares are pullbacks there since
their horizontal arrows are isomorphisms. Their vertical paste gives the composite square.

Compare the two structures on the primed row through the fully faithful bounded inclusions.
Pullback and its composition constraints restrict the same ambient pullbacks and constraints.
The open-extension and direct-image adjunctions restrict the same ambient adjunctions, so
their units, counits and the mates of pullback comparisons agree in these coordinates.
The chosen Nagata compactification depends only on the underlying morphism, by proof
irrelevance for the existence of a compactification. To compare any two compactifications,
use the same common proper refinement in both structures, giving the intermediate scheme its
structure via the projection. The comparison is the transition to the refinement followed by
the inverse transition. Each transition inserts the identity direct image, exchanges open
extension with proper direct image, and composes direct images. The direct-image constraints
are mates of the pullback constraints, and the middle exchange is the right mate of open base
change, whose inverse is itself a mate of the pullback square. Thus both transitions agree.

For each small square and the outer rectangle, compute slice base change using the chosen
unprimed compactification and its pullback. The base isomorphism and its pullback to the
compactification are weakly étale. The cross-field formula uses the same compactifications.
Its proper factor transposes to the pullback comparison followed by pullback of the counit.
Its inverse open factor transposes to pullback of the unit followed by the pullback comparison.
These are also the transposes in the slice, hence both factors agree. The final comparison
with the chosen primed compactification agrees by the common refinement computation.

Compute the primed composition isomorphism on the same compactification triangle for both
structures. Give each intermediate scheme its structure via the proper projection. The
triangle formula first compares the chosen composite compactification with that of the
triangle, then applies the inverse triangle isomorphism, then compares the two factor
compactifications with the chosen ones. The triangle isomorphism exchanges the middle open
extension and proper direct image and composes the two open extensions and two direct images.
The exchange agrees by the mate calculation above. Both composition constraints agree as
mates of pullback composition under their respective adjunctions. The outer compactification
comparisons agree by the common refinement calculation. Thus the slice composition
isomorphism has the specified primed component. Apply vertical pasting in the common slice
to the two squares at `A` and substitute these identifications on its two sides. -/
public theorem shriekCompositionUnderSchemeIsomorphisms
    {Ω : Type u} [Field Ω] (ℓ : ℕ) [Fact ℓ.Prime] [Fact (ringChar Ω).Prime]
    [Fact (ringChar Ω ≠ ℓ)]
    {U V W U' V' W' : Over (Spec (.of Ω))}
    [LocallyOfFiniteType U.hom] [QuasiCompact U.hom] [IsSeparated U.hom]
    [LocallyOfFiniteType V.hom] [QuasiCompact V.hom] [IsSeparated V.hom]
    [LocallyOfFiniteType W.hom] [QuasiCompact W.hom] [IsSeparated W.hom]
    [LocallyOfFiniteType U'.hom] [QuasiCompact U'.hom] [IsSeparated U'.hom]
    [LocallyOfFiniteType V'.hom] [QuasiCompact V'.hom] [IsSeparated V'.hom]
    [LocallyOfFiniteType W'.hom] [QuasiCompact W'.hom] [IsSeparated W'.hom]
    (f : U ⟶ V) (g : V ⟶ W) (f' : U' ⟶ V') (g' : V' ⟶ W')
    (tU : U'.left ≅ U.left) (tV : V'.left ≅ V.left) (tW : W'.left ≅ W.left)
    (sqf : IsPullback tU.hom f'.left f.left tV.hom) (sqg : IsPullback tV.hom g'.left g.left tW.hom)
    (A : Dᵇc(U.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (sqfg : IsPullback tU.hom (f' ≫ g').left (f ≫ g).left tW.hom := sqf.paste_vert sqg) :
    let FU := boundedConstructibleUpperStarOfMap ℓ (X := U) (Y := U') tU.hom
    let FW := boundedConstructibleUpperStarOfMap ℓ (X := W) (Y := W') tW.hom
    let Ef := purityFieldLowerShriekBaseChange ℓ f f' sqf
    let Eg := purityFieldLowerShriekBaseChange ℓ g g' sqg
    let Efg := purityFieldLowerShriekBaseChange ℓ (f ≫ g) (f' ≫ g') sqfg
    let C := boundedConstructibleLowerShriekComp_padicAlgCl ℓ f g
    let C' := boundedConstructibleLowerShriekComp_padicAlgCl ℓ f' g'
    Efg.hom.app A ≫ C'.hom.app (FU.obj A) =
      FW.map (C.hom.app A) ≫ Eg.hom.app ((boundedConstructibleLowerShriek ℓ f).obj A) ≫
        (boundedConstructibleLowerShriek ℓ g').map (Ef.hom.app A) := by
  intro FU FW Ef Eg Efg C C'
  let U₁ := Over.mk (tU.hom ≫ U.hom)
  let V₁ := Over.mk (tV.hom ≫ V.hom)
  let W₁ := Over.mk (tW.hom ≫ W.hom)
  have : LocallyOfFiniteType U₁.hom := inferInstanceAs (LocallyOfFiniteType (tU.hom ≫ U.hom))
  have : QuasiCompact U₁.hom := inferInstanceAs (QuasiCompact (tU.hom ≫ U.hom))
  have : IsSeparated U₁.hom := inferInstanceAs (IsSeparated (tU.hom ≫ U.hom))
  have : LocallyOfFiniteType V₁.hom := inferInstanceAs (LocallyOfFiniteType (tV.hom ≫ V.hom))
  have : QuasiCompact V₁.hom := inferInstanceAs (QuasiCompact (tV.hom ≫ V.hom))
  have : IsSeparated V₁.hom := inferInstanceAs (IsSeparated (tV.hom ≫ V.hom))
  have : LocallyOfFiniteType W₁.hom := inferInstanceAs (LocallyOfFiniteType (tW.hom ≫ W.hom))
  have : QuasiCompact W₁.hom := inferInstanceAs (QuasiCompact (tW.hom ≫ W.hom))
  have : IsSeparated W₁.hom := inferInstanceAs (IsSeparated (tW.hom ≫ W.hom))
  have wf : f'.left ≫ (tV.hom ≫ V.hom) = tU.hom ≫ U.hom := by
    rw [← sqf.w_assoc, Over.w]
  have wg : g'.left ≫ (tW.hom ≫ W.hom) = tV.hom ≫ V.hom := by
    rw [← sqg.w_assoc, Over.w]
  have wfg : (f' ≫ g').left ≫ (tW.hom ≫ W.hom) = tU.hom ≫ U.hom := by
    change (f'.left ≫ g'.left) ≫ (tW.hom ≫ W.hom) = tU.hom ≫ U.hom
    rw [Category.assoc, wg, wf]
  let f₁ : U₁ ⟶ V₁ := Over.homMk f'.left wf
  let g₁ : V₁ ⟶ W₁ := Over.homMk g'.left wg
  let x : U₁ ⟶ U := Over.homMk tU.hom rfl
  let y : V₁ ⟶ V := Over.homMk tV.hom rfl
  let z : W₁ ⟶ W := Over.homMk tW.hom rfl
  have sy : WeaklyEtale y.left := inferInstanceAs (WeaklyEtale tV.hom)
  have sz : WeaklyEtale z.left := inferInstanceAs (WeaklyEtale tW.hom)
  have sf : IsPullback x f₁ f y :=
    IsPullback.of_map (Over.forget _) (Over.OverMorphism.ext sqf.w) sqf
  have sg : IsPullback y g₁ g z :=
    IsPullback.of_map (Over.forget _) (Over.OverMorphism.ext sqg.w) sqg
  have sfg := sf.paste_vert sg
  have ef := sliceBaseChange_changePrimedStructure ℓ f f' wf (p' := f₁) rfl sf Ef (by rfl) A
  have eg := sliceBaseChange_changePrimedStructure ℓ g g' wg (p' := g₁) rfl sg Eg (by rfl)
    ((boundedConstructibleLowerShriek ℓ f).obj A)
  have efg := sliceBaseChange_changePrimedStructure ℓ (f ≫ g) (f' ≫ g') wfg
    (p' := f₁ ≫ g₁) (Over.OverMorphism.ext rfl) sfg Efg (by rfl) A
  have comp₁ := shriekCompositionIso_changeStructure ℓ f' g' wf wg
  have pasted := boundedConstructibleLowerShriekBaseChange_padicAlgCl_paste_vert_of_eq ℓ
    sfg sf sg rfl rfl A
  simp only [boundedConstructibleLowerShriekCompOfEq, eqToIso_refl, Iso.refl_trans] at pasted
  rw [eq_of_heq efg, eq_of_heq eg, eq_of_heq ef, comp₁] at pasted
  exact_by_kernel pasted

end WeilII
