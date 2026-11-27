module

public import WeilII.AlgebraicGeometry.IhomLissePrecomp
public import WeilConjectures.EtaleCohomology.Purity.RealSheaves.LisseWeilSheafTensor
public import WeilConjectures.WeilSheaf.LisseLocus
public import WeilConjectures.WeilSheaf.Localization
import WeilII.AlgebraicGeometry.IhomLisseTensorLisseAdjunction
import WeilII.AlgebraicGeometry.ClosedDirectImageLisseIhomProjection
import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates

/-!
# Lisse coefficients and exceptional pullback along a closed immersion

SGA 4, Exposé XVI, Corollary 3.8, uses the pairing with the restricted coefficient sheaf in
relative purity. Here the closed direct-image formula for internal Hom gives the corresponding
isomorphism for bounded constructible Weil complexes by adjunction.
-/

open AlgebraicGeometry CategoryTheory

namespace WeilII

universe u

/-- For a closed immersion `i`, the isomorphism `i^*A ⊗ Ri^!M ≅ Ri^!(A ⊗ M)` is natural in
the complex `M` and in every morphism of lisse Weil sheaves `A ⟶ A'`.

Write `I = Ri_*`, `S = Ri^!`, `a = i^*A`, `H_A = R𝓗om(A, −)` and `T_A = R𝓗om(A∨, −)`.
Use the closed-support adjunction of `WeilConjectures.WeilSheaf.Localization` and the lisse
internal-Hom projection formula for the closed direct image (for fixed coefficients, see
`WeilConjectures.WeilSheaf.ProjectionFormulaLisse.LowerShriek`). For any test complex `B`
on the closed subscheme, transpose `B ⟶ T_a(S M)` first under `H_a ⊣ T_a` and then under
`I ⊣ S` to get `I(H_a B) ⟶ M`. Precompose with the projection isomorphism
`H_A(I B) ≅ I(H_a B)`, then transpose under `H_A ⊣ T_A` and `I ⊣ S` to get
`B ⟶ S(T_A M)`. All four transpositions are bijections, and the inverse uses the inverse
projection isomorphism. The composite is natural in `B` and `M`. Applying it and its inverse
to the respective identity maps gives mutually inverse arrows by Yoneda, natural in `M`.

For `f : A ⟶ A'`, postcomposition on the initial Hom set by the tensor map for `i^*f`
transposes to precomposition by `I(H(i^*f)_B)`. The coefficient square for the projection
isomorphism moves that precomposition to `H(f)_(I B)`. The last two transpositions turn it
into postcomposition by `S(T(f)_M)`, where the tensor map is precomposition by `f∨`.
Evaluating at the identity gives the displayed coefficient square. -/
public theorem lisseClosedPullbackCoprojection
    {k : Type u} [Field k] [Finite k] {ℓ : ℕ} [Fact ℓ.Prime] [Fact (ringChar k ≠ ℓ)]
    {X Z U : Scheme.{u}} [X.Over (Spec (.of k))] [Z.Over (Spec (.of k))] [U.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    (i : Z ⟶ X) [IsClosedImmersion i] [i.IsOver (Spec (.of k))]
    (j : U ⟶ X) [IsOpenImmersion j] [j.IsOver (Spec (.of k))]
    (hij : IsCompl (Set.range i.base) (Set.range j.base)) :
    letI := isNoetherian_of_locallyOfFiniteType (X ↘ Spec (.of k))
    letI := locallyOfFiniteType_over_of_isOver i (S := Spec (.of k))
    let S := WeilComplex.closedUpperShriek (k₀ := k) (l := ℓ) i j hij
    let pull := WeilSheaf.upperStar (k₀ := k) (l := ℓ) i
    ∃ e : ∀ (A : WeilSheaf k ℓ X) (hA : A.IsLisse),
        S ⋙ WeilComplex.tensorLisse (pull.obj A) (hA.upperStar i) ≅
          WeilComplex.tensorLisse A hA ⋙ S,
      ∀ (A A' : WeilSheaf k ℓ X) (hA : A.IsLisse) (hA' : A'.IsLisse) (f : A ⟶ A')
          (M : WeilComplex k ℓ X),
        let ha := hA.upperStar i
        let ha' := hA'.upperStar i
        (ihomLissePrecomp (WeilSheaf.dualMap (pull.map f) ha ha') ha'.dual ha.dual).app (S.obj M) ≫
            (e A' hA').hom.app M =
          (e A hA).hom.app M ≫ S.map
            ((ihomLissePrecomp (WeilSheaf.dualMap f hA hA') hA'.dual hA.dual).app M) := by
  have := isNoetherian_of_locallyOfFiniteType (X ↘ Spec (.of k))
  have := locallyOfFiniteType_over_of_isOver i (S := Spec (.of k))
  intro S pull
  let push := WeilComplex.derivedLowerStar (k₀ := k) (l := ℓ) i
  let a : push ⊣ S := WeilComplex.closedUpperShriekAdjunction i j hij
  have coefficients (V : Scheme.{u}) [V.Over (Spec (.of k))]
      [LocallyOfFiniteType (V ↘ Spec (.of k))] :
      ∃ adj : ∀ (A : WeilSheaf k ℓ V) (hA : A.IsLisse),
          WeilComplex.ihomLisse A hA ⊣ WeilComplex.tensorLisse A hA,
        ∀ (A A' : WeilSheaf k ℓ V) (hA : A.IsLisse) (hA' : A'.IsLisse) (f : A ⟶ A'),
          conjugateEquiv (adj A hA) (adj A' hA') (ihomLissePrecomp f hA hA') =
            ihomLissePrecomp (WeilSheaf.dualMap f hA hA') hA'.dual hA.dual := by
    obtain ⟨adj, h⟩ := exists_ihomLisse_tensorLisse_adjunction (k := k) (ℓ := ℓ) V
    refine ⟨adj, ?_⟩
    intro A A' hA hA' f
    apply conjugateEquiv_eq_of_unit
    intro B
    have hu := h A A' hA hA' f B _ (𝟙 ((WeilComplex.ihomLisse A hA).obj B))
    erw [Category.comp_id, (adj A hA).homEquiv_id B] at hu
    exact hu.symm
  obtain ⟨adjX, hAdjX⟩ := coefficients X
  obtain ⟨adjZ, hAdjZ⟩ := coefficients Z
  obtain ⟨p, hp⟩ := closedDirectImageLisseIhomProjection (k := k) (ℓ := ℓ) i
  let adjPull (A : WeilSheaf k ℓ X) (hA : A.IsLisse) := adjZ (pull.obj A) (hA.upperStar i)
  let e (A : WeilSheaf k ℓ X) (hA : A.IsLisse) :=
    conjugateIsoEquiv ((adjPull A hA).comp a) (a.comp (adjX A hA)) (p A hA)
  refine ⟨e, ?_⟩
  intro A A' hA hA' f M
  let sz := ihomLissePrecomp (pull.map f) (hA.upperStar i) (hA'.upperStar i)
  let sx := ihomLissePrecomp f hA hA'
  have square : (p A' hA').hom ≫ Functor.whiskerRight sz push =
      Functor.whiskerLeft push sx ≫ (p A hA).hom :=
    NatTrans.ext (funext (hp A A' hA hA' f))
  have eq := congrArg (conjugateEquiv ((adjPull A hA).comp a) (a.comp (adjX A' hA'))) square
  rw [← conjugateEquiv_comp _ ((adjPull A' hA').comp a),
    ← conjugateEquiv_comp _ (a.comp (adjX A hA)),
    conjugateEquiv_whiskerRight, conjugateEquiv_whiskerLeft] at eq
  rw [hAdjZ (pull.obj A) (pull.obj A') (hA.upperStar i) (hA'.upperStar i) (pull.map f),
    hAdjX A A' hA hA' f] at eq
  exact NatTrans.congr_app eq M

end WeilII
