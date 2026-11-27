module

public import WeilII.CategoryTheory.OpenProperProjectionComponents
public import WeilConjectures.WeilSheaf.SmoothUnitBaseChangeEtale
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.CompactificationIndependence
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedPullbackCoherence

/-! # Lifting pasting of derived pullback squares -/

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.ProEtale AlgebraicGeometry.ProEtale.CondensedRing
open scoped CategoryTheory.Obj

namespace WeilII

universe u

/-- Suppose three bounded pullback square isomorphisms have the ambient forward square
comparisons as their inverse components under the full-subcategory inclusions. Then the
outer bounded square is the paste of the two inner squares, with the two vertical
composition comparisons on the ends.

Proof. Substitute the factorization equalities for the outer vertical arrows. At an
object B form the composite of the source horizontal pullback applied to the unprimed
composition isomorphism, the first inner square at the pullback of B along the second vertical arrow,
the primed first vertical pullback of the second inner square at B, and the inverse primed composition
isomorphism at the horizontally pulled-back B. Compare its inverse with the inverse
outer square using the faithful bounded inclusion. The map of a composite is the
composite of the maps. Apply the assumptions on all three square components. The bounded
inclusion sends both bounded composition components to those of the ambient derived
composition isomorphisms (`boundedConstructibleUpperStarComp_hom_app_hom` and
`boundedConstructibleUpperStarComp_inv_app_hom`). Each bounded pullback acts on
underlying morphisms by derived pullback. The resulting identity, with the four factors
in reverse order, is `pullbackSquareComparison_paste_horizontal` in pinned
WeilConjectures, `Derived/Condensed/CondensedPullbackCoherence.lean`, line 81.
Faithfulness gives equality of inverses, hence equality of the forward components. -/
public theorem boundedPullbackComparison_paste_of_inverse_app
    {k k' : Type u} [Field k] [Field k'] (ℓ : ℕ) [Fact ℓ.Prime]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    [Fact (ringChar k').Prime] [Fact (ringChar k' ≠ ℓ)]
    {X Z Y : Over (Spec (.of k))} {X' Z' Y' : Over (Spec (.of k'))}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom] [IsSeparated X'.hom]
    [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom] [IsSeparated Y'.hom]
    [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]
    [LocallyOfFiniteType Z'.hom] [QuasiCompact Z'.hom] [IsSeparated Z'.hom]
    {f : X ⟶ Y} {f' : X' ⟶ Y'} {i : X ⟶ Z} {g : Z ⟶ Y} {i' : X' ⟶ Z'} {g' : Z' ⟶ Y'}
    {p : X'.left ⟶ X.left} {v : Z'.left ⟶ Z.left} {q : Y'.left ⟶ Y.left}
    (sf : CommSq p f'.left f.left q) (si : CommSq p i'.left i.left v)
    (sg : CommSq v g'.left g.left q) (hf : i ≫ g = f) (hf' : i' ≫ g' = f')
    (I : (boundedConstructibleUpperStarOfMap ℓ (X := Z) (Y := X) i.left) ⋙
        (boundedConstructibleUpperStarOfMap ℓ (X := X) (Y := X') p) ≅
      (boundedConstructibleUpperStarOfMap ℓ (X := Z) (Y := Z') v) ⋙
        (boundedConstructibleUpperStarOfMap ℓ (X := Z') (Y := X') i'.left))
    (hI : ∀ (B : Dᵇc(Z.left)⟦Profinite.padicAlgClRingObj ℓ⟧), (I.inv.app B).hom =
      (pullbackSquareComparison (Profinite.padicAlgClRingObj ℓ) si).hom.app B.obj)
    (G : (boundedConstructibleUpperStarOfMap ℓ (X := Y) (Y := Z) g.left) ⋙
        (boundedConstructibleUpperStarOfMap ℓ (X := Z) (Y := Z') v) ≅
      (boundedConstructibleUpperStarOfMap ℓ (X := Y) (Y := Y') q) ⋙
        (boundedConstructibleUpperStarOfMap ℓ (X := Y') (Y := Z') g'.left))
    (hG : ∀ (B : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧), (G.inv.app B).hom =
      (pullbackSquareComparison (Profinite.padicAlgClRingObj ℓ) sg).hom.app B.obj)
    (F : (boundedConstructibleUpperStarOfMap ℓ (X := Y) (Y := X) f.left) ⋙
        (boundedConstructibleUpperStarOfMap ℓ (X := X) (Y := X') p) ≅
      (boundedConstructibleUpperStarOfMap ℓ (X := Y) (Y := Y') q) ⋙
        (boundedConstructibleUpperStarOfMap ℓ (X := Y') (Y := X') f'.left))
    (hF : ∀ (B : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧), (F.inv.app B).hom =
      (pullbackSquareComparison (Profinite.padicAlgClRingObj ℓ) sf).hom.app B.obj) :
    @IsPullbackComparisonPaste _ _ _ _ _ _ _ _ _ _ _ _
      (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ i)
      (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ g)
      (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ i')
      (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ g')
      (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ f)
      (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ f')
      (boundedConstructibleUpperStarOfMap ℓ (X := Y) (Y := Y') q)
      (boundedConstructibleUpperStarOfMap ℓ (X := Z) (Y := Z') v)
      (boundedConstructibleUpperStarOfMap ℓ (X := X) (Y := X') p)
      I.symm G.symm F.symm
      (boundedConstructibleUpperStarTriangleComparison (Profinite.padicAlgClRingObj ℓ) ℓ hf)
      (boundedConstructibleUpperStarTriangleComparison (Profinite.padicAlgClRingObj ℓ) ℓ hf') := by
  revert sf F
  cases hf
  cases hf'
  intro sf F hF B
  simp only [Iso.symm_inv, boundedConstructibleUpperStarTriangleComparison, eqToIso_refl,
    Iso.refl_trans]
  let P := boundedConstructibleUpperStarOfMap ℓ (X := X) (Y := X') p
  let Q := boundedConstructibleUpperStarOfMap ℓ (X := Y) (Y := Y') q
  have liftPaste {C : Type _} [Category.{_} C] {R : ObjectProperty C}
      {X₀ X₁ X₂ X₃ X₄ : C} {t : X₄ ⟶ X₀} {a : X₁ ⟶ X₀} {b : X₂ ⟶ X₁}
      {c : X₃ ⟶ X₂} {d : X₄ ⟶ X₃} (h : t = d ≫ c ≫ b ≫ a)
      {A₀ A₁ A₂ A₃ A₄ : R.FullSubcategory} (T : A₀ ≅ A₄)
      (A : A₀ ≅ A₁) (B : A₁ ≅ A₂) (C' : A₂ ≅ A₃) (D : A₃ ≅ A₄)
      (h₀ : A₀.obj = X₀) (h₁ : A₁.obj = X₁) (h₂ : A₂.obj = X₂)
      (h₃ : A₃.obj = X₃) (h₄ : A₄.obj = X₄)
      (ht : HEq T.inv.hom t) (ha : HEq A.inv.hom a) (hb : HEq B.inv.hom b)
      (hc : HEq C'.inv.hom c) (hd : HEq D.inv.hom d) :
      T.hom = A.hom ≫ B.hom ≫ C'.hom ≫ D.hom := by
    subst X₀ X₁ X₂ X₃ X₄
    apply (Iso.inv_eq_inv T (A ≪≫ B ≪≫ C' ≪≫ D)).mp
    apply ObjectProperty.hom_ext
    cases eq_of_heq ht
    cases eq_of_heq ha
    cases eq_of_heq hb
    cases eq_of_heq hc
    cases eq_of_heq hd
    simpa only [Iso.trans_inv, ObjectProperty.FullSubcategory.comp_hom, Category.assoc] using h
  let comp := boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ i g
  let comp' := boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ i' g'
  let ambientComp := CondensedRing.leftDerivedUpperStarComp (Profinite.padicAlgClRingObj ℓ)
    i.left g.left
  let incl := (boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left)).ι
  have hcomp : (comp.inv.app B).hom = ambientComp.inv.app B.obj :=
    (Iso.inv_eq_inv (incl.mapIso (comp.app B)) (ambientComp.app B.obj)).mpr
      (boundedConstructibleUpperStarComp_hom_app_hom (Profinite.padicAlgClRingObj ℓ) ℓ i g B)
  have hpaste :=
    pullbackSquareComparison_paste_horizontal (Profinite.padicAlgClRingObj ℓ) si sg B.obj
  have primeComp :=
    boundedConstructibleUpperStarComp_hom_app_hom (Profinite.padicAlgClRingObj ℓ) ℓ i' g' (Q.obj B)
  have innerI := hI ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ g).obj B)
  have innerG :=
    boundedConstructibleUpperStar_map_hom (Profinite.padicAlgClRingObj ℓ) ℓ i' (G.inv.app B)
  rw [hG B] at innerG
  have outerComp := congrArg (fun m ↦ m.hom)
    (boundedConstructibleUpperStarOfMap_map ℓ (X := X) (Y := X') p (comp.inv.app B))
  dsimp only [ObjectProperty.homMk] at outerComp
  rw [hcomp] at outerComp
  have bounded := liftPaste
    (R := boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X'.left))
    hpaste (F.app B) (P.mapIso (comp.app B))
    (I.app ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ g).obj B))
    ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ i').mapIso (G.app B))
    (comp'.app (Q.obj B)).symm
  refine bounded rfl rfl rfl rfl rfl ?_ ?_ ?_ ?_ ?_
  · transport_exact heq_of_eq (hF B)
  case' refine_2 => have h := heq_of_eq outerComp
  case' refine_3 => have h := heq_of_eq innerI
  case' refine_4 => have h := heq_of_eq innerG
  case' refine_5 => have h := heq_of_eq primeComp
  all_goals
    dsimp +instances +zetaDelta only [Functor.comp_obj, Iso.app, Iso.symm, Functor.mapIso,
      ObjectProperty.homMk] at h ⊢
    transport_exact h

end WeilII
