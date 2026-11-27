module

public import WeilII.AlgebraicGeometry.IhomLissePrecomp
import WeilII.AlgebraicGeometry.LowerStarIhomCoefficientNaturality
import WeilII.CategoryTheory.FullSubcategorySquare
public import WeilConjectures.WeilSheaf.LisseLocus
public import WeilConjectures.WeilSheaf.LowerStar
import WeilConjectures.WeilSheaf.Localization
import WeilConjectures.WeilSheaf.ProjectionFormulaLisse.LowerStar

/-!
# Closed direct image and internal Hom from a lisse Weil sheaf

The sheaf-level comparison is the mate constructed in
`WeilConjectures.WeilSheaf.ProjectionFormulaLisse.LowerStar`. Exactness of closed direct
image passes its coefficient naturality to bounded constructible Weil complexes.
-/

open AlgebraicGeometry CategoryTheory

namespace WeilII

universe u

/-- The isomorphism `R𝓗om(A, Ri_* B) ≅ Ri_* R𝓗om(i^* A, B)` is natural in the Weil
complex `B` and contravariantly natural in the lisse Weil sheaf `A`.

On pro-étale Weil sheaves write `L = i^*`, `J = i_*`, and `h_A = [A, −]`.
In `WeilConjectures.WeilSheaf.ProjectionFormulaLisse.LowerStar` the map
`π : h_A(J N) ⟶ J(h_(L A) N)` is an isomorphism. Its transpose under `L ⊣ J` is the
pullback comparison followed by `h_(L A)` applied to the counit at `N`. For `f : A ⟶ A'`,
the pullback comparison commutes with precomposition by `f`, as can be checked on geometric
sheaves by `adicUpperStarIhomComparison_ihomMap`. Precomposition by `L f` commutes with the
counit by naturality in the second argument of internal Hom. Transposing the resulting
equality back gives the coefficient square for `π`.

The finite-type scheme `X` is Noetherian, so the complementary open immersion is quasi-compact.
Thus `J` preserves finite colimits by `WeilConjectures.WeilSheaf.Localization` and finite limits
as a right adjoint. Both internal Hom functors are left exact and preserve finite
colimits because their source coefficients are lisse. Apply the sheaf isomorphisms degreewise.
Naturality in the differential gives chain isomorphisms, and naturality in chain maps makes
these natural on the homotopy category. All functors involved are exact, so the derived units
identify their termwise action after localization with their total right derived functors.
Under these identifications the derived precomposition maps are the termwise maps, by the
defining unit equation for a right derived natural transformation. Precomposition with the
localization is fully faithful, so the isomorphism and its coefficient square descend to the
derived categories. The functors preserve bounded constructible objects, and restriction to
those full subcategories gives the asserted isomorphism and equality. -/
public theorem closedDirectImageLisseIhomProjection
    {k : Type u} [Field k] [Finite k] {ℓ : ℕ} [Fact ℓ.Prime] [Fact (ringChar k ≠ ℓ)]
    {X Z : Scheme.{u}} [X.Over (Spec (.of k))] [Z.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    (i : Z ⟶ X) [IsClosedImmersion i] [i.IsOver (Spec (.of k))] :
    letI := locallyOfFiniteType_over_of_isOver i (S := Spec (.of k))
    let push := WeilComplex.derivedLowerStar (k₀ := k) (l := ℓ) i
    let pull := WeilSheaf.upperStar (k₀ := k) (l := ℓ) i
    ∃ p : ∀ (A : WeilSheaf k ℓ X) (hA : A.IsLisse),
        push ⋙ WeilComplex.ihomLisse A hA ≅
          WeilComplex.ihomLisse (pull.obj A) (hA.upperStar i) ⋙ push,
      ∀ (A A' : WeilSheaf k ℓ X) (hA : A.IsLisse) (hA' : A'.IsLisse) (f : A ⟶ A')
          (B : WeilComplex k ℓ Z),
        (p A' hA').hom.app B ≫
            push.map ((ihomLissePrecomp (pull.map f) (hA.upperStar i) (hA'.upperStar i)).app B) =
          (ihomLissePrecomp f hA hA').app (push.obj B) ≫ (p A hA).hom.app B := open Limits in by
  intro push pull
  have := locallyOfFiniteType_over_of_isOver i (S := Spec (.of k))
  let J := ProEtaleWeilSheaf.lowerStar k ℓ i
  have := isNoetherian_of_locallyOfFiniteType (X ↘ Spec (.of k))
  have : PreservesFiniteColimits J :=
    ProEtaleWeilSheaf.preservesFiniteColimits_lowerStar_of_isCompl i i.openComplement.ι
      (eq_compl_iff_isCompl.mp i.range_eq_compl_range_openComplement_ι)
  let Lisse := Subtype (WeilSheaf.IsLisse : WeilSheaf k ℓ X → Prop)
  let F (a : Lisse) := (ProEtaleWeilSheaf.ihomBifunctor k ℓ X).obj (Opposite.op a.val.obj)
  let G (a : Lisse) := (ProEtaleWeilSheaf.ihomBifunctor k ℓ Z).obj (Opposite.op (pull.obj a.val).obj)
  have : ∀ a, PreservesFiniteLimits (F a) :=
    fun a ↦ inferInstanceAs (PreservesFiniteLimits (ProEtaleWeilSheaf.ihomFunctor k ℓ X a.val.obj))
  have : ∀ a, PreservesFiniteLimits (G a) :=
    fun a ↦ inferInstanceAs (PreservesFiniteLimits
      (ProEtaleWeilSheaf.ihomFunctor k ℓ Z (pull.obj a.val).obj))
  have : ∀ a, PreservesFiniteColimits (F a) :=
    fun a ↦ ProEtaleWeilSheaf.preservesFiniteColimits_ihomFunctor _ a.property
  have : ∀ a, PreservesFiniteColimits (G a) :=
    fun a ↦ ProEtaleWeilSheaf.preservesFiniteColimits_ihomFunctor _ (a.property.upperStar i)
  let P := WeilComplex.objectProperty k ℓ Z
  let P' := WeilComplex.objectProperty k ℓ X
  have hJ : ∀ K, P K → P' (J.rightDerivedFunctor.obj K) :=
    WeilComplex.objectProperty_rightDerivedLowerStar i
  have hF (a : Lisse) : ∀ K, P' K → P' ((F a).rightDerivedFunctor.obj K) :=
    WeilComplex.objectProperty_rightDerivedFunctor_ihomFunctor a.val a.property
  have hG (a : Lisse) : ∀ K, P K → P ((G a).rightDerivedFunctor.obj K) :=
    WeilComplex.objectProperty_rightDerivedFunctor_ihomFunctor (pull.obj a.val)
      (a.property.upperStar i)
  let src (A : WeilSheaf k ℓ X) (hA : A.IsLisse) := WeilComplex.ihomLisse A hA
  let dst (A : WeilSheaf k ℓ X) (hA : A.IsLisse) := WeilComplex.ihomLisse (pull.obj A) (hA.upperStar i)
  let e (a : Lisse) : J ⋙ F a ≅ G a ⋙ J :=
    ProEtaleWeilSheaf.lowerStarCompIhomFunctorIso i a.val.obj a.property
  let Arr (A B : WeilSheaf k ℓ X) := A ⟶ B
  let f (a b : Lisse) (u : Arr b.val a.val) : F a ⟶ F b :=
    (ProEtaleWeilSheaf.ihomBifunctor k ℓ X).map u.hom.op
  let g (a b : Lisse) (u : Arr b.val a.val) : G a ⟶ G b :=
    (ProEtaleWeilSheaf.ihomBifunctor k ℓ Z).map (pull.map u).hom.op
  let s (A B : WeilSheaf k ℓ X) (hA : A.IsLisse) (hB : B.IsLisse) (u : Arr A B) : src B hB ⟶ src A hA :=
    ihomLissePrecomp u hA hB
  let t (A B : WeilSheaf k ℓ X) (hA : A.IsLisse) (hB : B.IsLisse) (u : Arr A B) : dst B hB ⟶ dst A hA :=
    ihomLissePrecomp (pull.map u) (hA.upperStar i) (hB.upperStar i)
  have hs (a b : Lisse) (u : Arr b.val a.val) : HEq (s b.val a.val b.property a.property u) (P'.liftFullSubcategoryMap P'
      (Functor.rightDerivedFunctorNatTrans (f a b u)) (hF a) (hF b)) := HEq.rfl
  have ht (a b : Lisse) (u : Arr b.val a.val) : HEq (t b.val a.val b.property a.property u) (P.liftFullSubcategoryMap P
      (Functor.rightDerivedFunctorNatTrans (g a b u)) (hG a) (hG b)) := HEq.rfl
  have h (a b : Lisse) (u : Arr b.val a.val) (N : ProEtaleWeilSheaf k ℓ Z) :
      (e a).hom.app N ≫ J.map ((g a b u).app N) =
        (f a b u).app (J.obj N) ≫ (e b).hom.app N := by
    dsimp only [e, J, f, g, pull, WeilSheaf.upperStar, ObjectProperty.liftFullSubcategory_map,
      ObjectProperty.homMk_hom]
    exact lowerStarIhomCoefficientNaturality i u.hom b.property a.property N
  have result := fullSubcategoryExactRightDerivedSquare J WeilSheaf.IsLisse F G e P P' hJ hF hG
    (C' := WeilComplex k ℓ Z) (D' := WeilComplex k ℓ X)
    (cC := instCategoryWeilComplex) (cD := instCategoryWeilComplex) rfl rfl HEq.rfl HEq.rfl
    push src dst HEq.rfl (fun _ ↦ HEq.rfl) (fun _ ↦ HEq.rfl) Arr f g s t hs ht h
  exact result

end WeilII
