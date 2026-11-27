module

public import WeilConjectures.AlgebraicGeometry.AffineSpace.FieldPoints
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import WeilConjectures.WeilSheaf.TraceFunctionOps

/-! # Field points of a polynomial hypersurface

The change of variables on the hypersurface in Zhang, Lemma 2.2, equation (2.2.1). -/

open AlgebraicGeometry CategoryTheory

namespace WeilII

universe u

/-- The field points of the scheme cut out by a polynomial are exactly its zero tuples
over the extension field. The forward map reads the coordinates after the closed immersion.
Evaluating the section of the polynomial at a field point evaluates its coefficients along
the field extension. Thus a zero tuple determines a point factoring through the zero
subscheme, and the factorization is unique since the inclusion is a monomorphism.
Source: Zhang, equation (2.2.1), and the universal property of the zero subscheme. -/
@[expose] public noncomputable def affineHypersurfaceFieldPoints
    (k L : Type u) [Field k] [Field L] [Algebra k L] {n : ℕ} (P : MvPolynomial (Fin n) k) :
    let S := Spec (CommRingCat.of k)
    let X := 𝔸(ULift.{u} (Fin n); S)
    let coeff := ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ (X ↘ S).appTop).hom
    let p := MvPolynomial.eval₂Hom coeff (fun j : Fin n ↦ AffineSpace.coord S (ULift.up.{u} j)) P
    let i := X.zeroLocusSubschemeι {p}
    (i ≫ X ↘ S).fieldPoints L ≃ {x : Fin n → L // MvPolynomial.eval₂ (algebraMap k L) x P = 0} := by
  intro S X coeff p i
  let a := X ↘ S
  letI : (X.zeroLocusSubscheme {p}).Over S := ⟨i ≫ a⟩
  letI : i.IsOver S := ⟨rfl⟩
  let coordEquiv := (AffineSpace.fieldPointsEquivPi (ULift.{u} (Fin n)) k L).trans
    (Equiv.ulift.arrowCongr (Equiv.refl L))
  let val := (Scheme.ΓSpecIso (CommRingCat.of L)).hom
  have evaluation (x : a.fieldPoints L) :
      val (x.1.appTop p) = MvPolynomial.eval₂ (algebraMap k L) (coordEquiv x) P := by
    let atPoint := (x.1.appTop ≫ val).hom
    change atPoint (MvPolynomial.eval₂Hom coeff _ P) = _
    rw [MvPolynomial.map_eval₂Hom]
    have hc : atPoint.comp coeff = algebraMap k L := by
      change ((Scheme.ΓSpecIso (.of k)).inv ≫ a.appTop ≫ x.1.appTop ≫ val).hom = _
      rw [← Scheme.Hom.comp_appTop_assoc, x.2]
      dsimp only [val]
      rw [Scheme.ΓSpecIso_naturality, Iso.inv_hom_id_assoc]
      rfl
    rw [hc]
    rfl
  let f (y : (i ≫ a).fieldPoints L) :
      {x : Fin n → L // MvPolynomial.eval₂ (algebraMap k L) x P = 0} :=
    ⟨coordEquiv (i.mapFieldPoints L y), by
      rw [← evaluation]
      change val ((y.1 ≫ i).appTop p) = 0
      change val (y.1.appTop ((X.zeroLocusSubschemeι {p}).appTop p)) = 0
      rw [X.zeroLocusSubschemeι_appTop (Set.mem_singleton p), map_zero, map_zero]⟩
  refine Equiv.ofBijective f ⟨?_, ?_⟩
  · intro y z h
    have hh := coordEquiv.injective (congrArg Subtype.val h)
    exact Subtype.ext ((cancel_mono i).mp (congrArg Subtype.val hh))
  · rintro ⟨v, hv⟩
    let x := coordEquiv.symm v
    have hx : x.1.appTop p = 0 := by
      apply (Scheme.ΓSpecIso (.of L)).commRingCatIsoToRingEquiv.injective
      change val (x.1.appTop p) = val 0
      rw [evaluation, map_zero]
      simpa [x] using hv
    have vanish : ∀ t ∈ ({p} : Set Γ(X, ⊤)), x.1.appTop t = 0 := by simpa using hx
    let y := x.1.liftZeroLocusSubscheme vanish
    have hy : y ≫ i = x.1 := Scheme.Hom.liftZeroLocusSubscheme_zeroLocusSubschemeι _ _
    let point : (i ≫ a).fieldPoints L := ⟨y, by rw [← Category.assoc, hy]; exact x.2⟩
    have image : i.mapFieldPoints L point = x := Subtype.ext hy
    exact ⟨point, Subtype.ext ((congrArg coordEquiv image).trans (coordEquiv.apply_symm_apply v))⟩

end WeilII
