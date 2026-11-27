module

public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.LinearCombination
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.OfAmple
import WeilII.AlgebraicGeometry.PullbackSectionZeroComplement
import WeilConjectures.AlgebraicGeometry.Modules.PullbackFreeGenerator
import WeilConjectures.AlgebraicGeometry.Modules.PullbackSections
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
# The affine chart defined by a normalized hyperplane

Coordinate calculations for the chart used in Zhang, Construction 2.5.
-/

namespace WeilII

open AlgebraicGeometry CategoryTheory ProjectiveSpace Scheme.Modules

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Zhang, Construction 2.5. The complement of a hyperplane with last coefficient one
has affine coordinates given by the other homogeneous coordinates divided by its equation.
For a tuple with one coordinate equal to one, pulling back the chart amounts to inverting
the linear form evaluated on the tuple and dividing all its coordinates by that value.

On the complement the equation is a free generator of the twisting line, so division defines
the chart morphism. Its inverse is classified by the tuple consisting of the affine
coordinates and one minus their linear combination. These sections generate the unit module,
and their linear form equals one. The classification by generating sections identifies both
composites with the identity. On the distinguished standard chart of a tuple, its coordinates
are the pullbacks of the standard ratios, so the hyperplane equation pulls back to the
stated scalar times the distinguished generator. -/
public theorem normalizedHyperplaneChart (S : Scheme.{u}) [IsAffine S] (m : ℕ)
    (l : Fin m → Γ(S, ⊤)) :
    let J := ULift.{u} (Fin (m + 1))
    let P := ℙ(J; S)
    let A := 𝔸(ULift.{u} (Fin m); S)
    let z := twistOneSection J S
    ∀ (lam : Γ(twist J S 1, ⊤)),
    lam = z ⟨Fin.last m⟩ + ∑ j, (P ↘ S).appTop (l j) • z ⟨j.castSucc⟩ →
    let B := (homOfGlobalSection _ lam).zeroLocus.subschemeι.openComplement
    let y := fun j : Fin m ↦ AffineSpace.coord S (ULift.up.{u} j)
    let lamB : Γ(twistRestrict B.ι 1, ⊤) := pullbackSection B.ι lam
    ∃ chart : B.toScheme ≅ A,
      chart.hom ≫ A ↘ S = B.ι ≫ P ↘ S ∧
      (∀ j, chart.hom.appTop (y j) • lamB =
        pullbackSection B.ι (z ⟨j.castSucc⟩)) ∧
      ∀ (X : Scheme.{u}) [IsAffine X] (π : X ⟶ S) (w : J → Γ(X, ⊤)) (i : J)
        (_hi : w i = 1) (hw : Ideal.span (Set.range w) = ⊤),
        let f := homOfSections π w hw
        ∀ p : Γ(X, ⊤), p = w ⟨Fin.last m⟩ + ∑ j, π.appTop (l j) * w ⟨j.castSucc⟩ →
        let V := X.basicOpen p
        let g := AffineSpace.homOfVector (V.ι ≫ π) (fun j : ULift.{u} (Fin m) ↦
          X.divBasicOpen (w ⟨j.down.castSucc⟩) p)
        f ⁻¹ᵁ B = V ∧ g ≫ chart.inv ≫ B.ι = V.ι ≫ f := by
  classical
  intro J P A z lam hLam B y lamB
  let pull {T W : Scheme.{u}} (v : T ⟶ W) {M : W.Modules} (s : Γ(M, ⊤)) :
      Γ((pullback v).obj M, ⊤) := pullbackSection v s
  let L := twist J S 1
  let σ := homOfGlobalSection L lam
  have : IsAffine A := isAffine_of_isAffineHom (A ↘ S)
  have := IsInvertible.sheafOfModules_isInvertible L
  have hB : B = σ.zeroLocus.support.compl := by
    ext x
    simp only [B, Scheme.Hom.coe_openComplement, Scheme.IdealSheafData.range_subschemeι]
    rfl
  let res := L.presheaf.map (homOfLE (le_top : B ≤ ⊤)).op
  have gen : IsFreeGenerator (res lam) := by
    have H := isFreeGenerator_app_one_of_le σ hB.le
    change IsFreeGenerator ((homOfGlobalSection L lam).app B (1 : Γ(P, B))) at H
    rwa [homOfGlobalSection_app_one] at H
  let q (j : J) := gen.coeff (res (z j))
  have hq (j : J) : res (z j) = q j • res lam := (gen.coeff_smul _).symm
  let scal (j : J) := B.ι.appLE B ⊤ B.ι_preimage_self.ge (q j)
  let h := AffineSpace.homOfVector (B.ι ≫ P ↘ S)
    (fun j : ULift.{u} (Fin m) ↦ scal ⟨j.down.castSucc⟩)
  have hbase : h ≫ A ↘ S = B.ι ≫ P ↘ S := AffineSpace.homOfVector_over ..
  have hcoord (j : Fin m) : h.appTop (y j) = scal ⟨j.castSucc⟩ :=
    AffineSpace.homOfVector_appTop_coord ..
  have scal_apply {T : Scheme.{u}} (v : T ⟶ B.toScheme) (j : J) :
      v.appTop (scal j) = (v ≫ B.ι).appLE B ⊤ (fun x _ ↦ (v x).2) (q j) := by
    rw [← Scheme.Hom.appLE_top_top]
    change (B.ι.appLE B ⊤ B.ι_preimage_self.ge ≫ v.appLE ⊤ ⊤ le_top) (q j) = _
    rw [Scheme.Hom.appLE_comp_appLE]
  have ratio {T : Scheme.{u}} (f : T ⟶ P) (hD : ⊤ ≤ f ⁻¹ᵁ B) (j : J) :
      pull f (z j) = f.appLE B ⊤ hD (q j) • pull f lam := by
    let N := twistRestrict f 1
    have restrict (s : Γ(L, ⊤)) : N.presheaf.map (homOfLE hD).op
        (N.presheaf.map (homOfLE (le_top : f ⁻¹ᵁ B ≤ ⊤)).op (pull f s)) = pull f s :=
      (Scheme.Modules.presheaf_map_map_apply _ _ _).trans (Scheme.Modules.presheaf_map_id_apply _ _)
    have H := congrArg (N.presheaf.map (homOfLE hD).op)
      (pullbackSection_map_eq_smul f le_top (hq j))
    rw [Scheme.Modules.map_smul] at H
    exact (restrict (z j)).symm.trans (H.trans (congrArg (_ • ·) (restrict lam)))
  have all_coord {T : Scheme.{u}} (v : T ⟶ B.toScheme) (f : T ⟶ P) (fac : v ≫ B.ι = f) (j : J) :
      v.appTop (scal j) • pull f lam = pull f (z j) := by
    subst f
    rw [scal_apply]
    exact (ratio _ _ j).symm
  have bcoord (j : J) : scal j • lamB =
      pullbackSection B.ι (z j) := (ratio B.ι B.ι_preimage_self.ge j).symm
  -- The inverse chart is the projective tuple whose linear form is one.
  let rem := 1 - ∑ j, (A ↘ S).appTop (l j) * y j
  let w : J → Γ(A, ⊤) := fun j ↦ (Fin.snoc y rem : Fin (m + 1) → Γ(A, ⊤)) j.down
  have wlast : w ⟨Fin.last m⟩ = rem := Fin.snoc_last ..
  have wcast (j : Fin m) : w ⟨j.castSucc⟩ = y j := by simp [w]
  let O (j : J) := A.basicOpen (w j)
  have cover : ⨆ j, O j = ⊤ := by
    change ⨆ j, A.basicOpen (w j) = ⊤
    rw [← iSup_range', (isAffineOpen_top A).iSup_basicOpen_eq_self_iff]
    apply (Ideal.eq_top_iff_one _).mpr
    let I := Ideal.span (Set.range w)
    have wi (j : J) : w j ∈ I := Ideal.subset_span ⟨j, rfl⟩
    have hs : (∑ j, (A ↘ S).appTop (l j) * y j) ∈ I :=
      I.sum_mem fun j _ ↦ I.mul_mem_left _ (wcast j ▸ wi ⟨j.castSucc⟩)
    have hr : rem ∈ I := wlast ▸ wi ⟨Fin.last m⟩
    simpa [rem] using I.add_mem hr hs
  let u (j : J) : Γ(Scheme.Modules.unit A, ⊤) := w j
  have gu (j : J) : IsFreeGenerator ((Scheme.Modules.unit A).presheaf.map
      (homOfLE (le_top : O j ≤ ⊤)).op (u j)) := by
    have hu : IsUnit (A.presheaf.map (homOfLE (le_top : O j ≤ ⊤)).op (w j)) :=
      A.toRingedSpace.isUnit_res_basicOpen (w j)
    obtain ⟨v, hv⟩ := hu
    convert (isFreeGenerator_one (O j)).units_smul v using 1
    change A.presheaf.map _ (w j) = v.val * (1 : Γ(A, O j))
    rw [mul_one, hv]
  obtain ⟨k, kbase, ε, hεiso, hε⟩ := exists_hom_twistRestrict u O gu (A ↘ S) cover
  have ke (j : J) : ε.app ⊤ (pullbackSection k (z j)) = u j := by
    simpa only [Scheme.Hom.preimage_top, Scheme.Modules.presheaf_map_id_apply] using hε j
  let E : Γ(twistRestrict k 1, ⊤) := (inv ε).app ⊤ (1 : Γ(A, ⊤))
  have genE : IsFreeGenerator E := (isFreeGenerator_one (⊤ : A.Opens)).app_hom (asIso ε).symm
  have kcoord (j : J) : (pullbackSection k (z j) : Γ(twistRestrict k 1, ⊤)) = w j • E := by
    apply (ConcreteCategory.bijective_of_isIso (ε.app ⊤)).injective
    rw [ke, Hom.app_smul]
    change u j = w j • (inv ε ≫ ε).app ⊤ (1 : Γ(A, ⊤))
    simp only [IsIso.inv_hom_id, Hom.id_app]
    exact (mul_one (w j)).symm
  have eval_lam {T : Scheme.{u}} (v : T ⟶ P) (s : J → Γ(T, ⊤))
      (E : Γ(twistRestrict v 1, ⊤))
      (hs : ∀ j, (pullbackSection v (z j) : Γ(twistRestrict v 1, ⊤)) = s j • E) :
      pullbackSection v lam =
        (s ⟨Fin.last m⟩ + ∑ j, (v ≫ P ↘ S).appTop (l j) * s ⟨j.castSucc⟩) • E := by
    rw [hLam]
    change ((pullbackPushforwardAdjunction v).unit.app L).app ⊤ (_ + _) = _
    rw [map_add, map_sum, add_smul, Finset.sum_smul]
    refine congrArg₂ (· + ·) (hs _) (Finset.sum_congr rfl fun j _ ↦ ?_)
    change pullbackSection v ((P ↘ S).appTop (l j) • z ⟨j.castSucc⟩) = _
    rw [pullbackSection_smul, Scheme.Hom.comp_appTop, CommRingCat.comp_apply, mul_smul]
    exact congrArg (fun b : Γ(twistRestrict v 1, ⊤) ↦ v.appTop ((P ↘ S).appTop (l j)) • b) (hs _)
  have kLam : pullbackSection k lam = E := by
    rw [eval_lam k w E kcoord, kbase, wlast]
    simp only [wcast, rem, sub_add_cancel, one_smul]
  have kpre : k ⁻¹ᵁ B = ⊤ := by
    rw [preimage_zeroLocus_openComplement_eq_basicOpen k lam genE (r := 1) (by rw [one_smul, kLam])]
    exact A.basicOpen_one
  have krange : Set.range k ⊆ Set.range B.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨x, rfl⟩
    exact kpre.ge (show x ∈ (⊤ : A.Opens) from trivial)
  let invChart := IsOpenImmersion.lift B.ι k krange
  have kincl : invChart ≫ B.ι = k := IsOpenImmersion.lift_fac _ _ _
  have ki_h : invChart ≫ h = 𝟙 A := by
    apply AffineSpace.hom_ext
    · rw [Category.assoc, hbase, ← Category.assoc, kincl, kbase, Category.id_comp]
    · rintro ⟨j⟩
      change (invChart ≫ h).appTop (y j) = _
      rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, hcoord]
      have H := all_coord invChart k kincl ⟨j.castSucc⟩
      change invChart.appTop (scal ⟨j.castSucc⟩) • (pull k lam) = _ at H
      have kLam' : pull k lam = E := kLam
      rw [kLam'] at H
      have K : pull k (z ⟨j.castSucc⟩) = y j • E := (wcast j) ▸ kcoord ⟨j.castSucc⟩
      rw [K] at H
      exact genE.smul_left_injective H
  have genB : IsFreeGenerator lamB := by
    let τ := (pullbackObjUnitIso B.ι).inv ≫ (pullback B.ι).map σ
    have := IsInvertible.sheafOfModules_isInvertible (twistRestrict B.ι 1)
    have htop : ⊤ ≤ τ.zeroLocus.support.compl := by
      rw [compl_support_zeroLocus_pullback, ← hB]
      exact B.ι_preimage_self.ge
    have H := isFreeGenerator_app_one_of_le τ htop
    have hσ : σ.app ⊤ (1 : Γ(P, ⊤)) = lam := by
      rw [homOfGlobalSection_app_one, Scheme.Modules.presheaf_map_id_apply]
    have H' : τ.app ⊤ (1 : Γ(B, ⊤)) = lamB :=
      (pullbackSection_app_one B.ι σ).symm.trans (congrArg (pullbackSection B.ι) hσ)
    exact H' ▸ H
  have hscalar (j : J) : h.appTop (w j) = scal j := by
    obtain ⟨j⟩ := j
    induction j using Fin.lastCases with
    | cast j => rw [wcast, hcoord]
    | last =>
      have H := eval_lam B.ι scal lamB (fun j ↦ (bcoord j).symm)
      have one : (1 : Γ(B, ⊤)) =
          scal ⟨Fin.last m⟩ + ∑ j, (B.ι ≫ P ↘ S).appTop (l j) * scal ⟨j.castSucc⟩ :=
        genB.smul_left_injective ((one_smul _ _).trans H)
      simp only [wlast, rem, map_sub, map_one, map_sum, map_mul, hcoord]
      have eqc (j : Fin m) : h.appTop ((A ↘ S).appTop (l j)) = (B.ι ≫ P ↘ S).appTop (l j) := by
        rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, hbase]
      simp only [eqc]
      exact sub_eq_of_eq_add one
  -- In the λ frame, the inclusion of B is classified by the same tuple pulled back along h.
  let τ := homOfGlobalSection (twistRestrict B.ι 1) lamB
  have : IsIso τ := isIso_homOfGlobalSection genB
  let η := (pullbackObjUnitIso h).hom ≫ τ
  have : IsIso η := IsIso.comp_isIso
  let N := (pullback h).obj (Scheme.Modules.unit A)
  have transport (j : J) : N.presheaf.map (homOfLE (le_top : B.ι ⁻¹ᵁ ⊤ ≤ ⊤)).op
      (pullbackTopSection h (u j)) = pull h (u j) :=
    (Scheme.Modules.presheaf_map_map_apply _ _ _).trans (Scheme.Modules.presheaf_map_id_apply _ _)
  have unitCoord (j : J) : (pullbackObjUnitIso h).hom.app ⊤ (pull h (u j)) = h.appTop (w j) :=
    pullbackObjUnitIso_hom_app_pullbackSection h (w j)
  have compat (j : J) : (inv η).app _ (pullbackSection B.ι (z j)) =
      ((pullback h).obj (Scheme.Modules.unit A)).presheaf.map
        (homOfLE (le_top : B.ι ⁻¹ᵁ ⊤ ≤ ⊤)).op (pullbackTopSection h (u j)) := by
    apply (ConcreteCategory.bijective_of_isIso (η.app ⊤)).injective
    change (inv η ≫ η).app ⊤ _ = η.app ⊤ _
    rw [IsIso.inv_hom_id, Hom.id_app]
    change pullbackSection B.ι (z j) = η.app ⊤ _
    rw [transport j]
    change _ = τ.app ⊤ ((pullbackObjUnitIso h).hom.app ⊤ (pull h (u j)))
    rw [unitCoord]
    change pullbackSection B.ι (z j) = (homOfGlobalSection _ lamB).app ⊤ (h.appTop (w j))
    rw [homOfGlobalSection_app, Scheme.Modules.presheaf_map_id_apply, hscalar, bcoord]
  have h_ki : h ≫ invChart = 𝟙 _ := by
    apply (cancel_mono B.ι).mp
    rw [Category.assoc, kincl, Category.id_comp]
    have eqn := map_comp_eq_of_pullbackTopSection (𝟙 S) h ε hε (inv η) compat
      (by rw [Category.comp_id, kbase, hbase])
    simpa only [ProjectiveSpace.map_id, Category.comp_id] using eqn.symm
  let chart : B.toScheme ≅ A := ⟨h, invChart, h_ki, ki_h⟩
  refine ⟨chart, hbase, fun j ↦ (hcoord j) ▸ bcoord ⟨j.castSucc⟩, ?_⟩
  intro X hX π s i hi hs f p hp V g
  have on_tuple {T : Scheme.{u}} (π' : T ⟶ S) (s' : J → Γ(T, ⊤))
      (hs' : Ideal.span (Set.range s') = ⊤) (hi' : s' i = 1) :
      let f' := homOfSections π' s' hs'
      let E' := pull f' (z i)
      IsFreeGenerator E' ∧ (∀ j, pull f' (z j) = s' j • E') ∧
        pull f' lam = (s' ⟨Fin.last m⟩ + ∑ j, π'.appTop (l j) * s' ⟨j.castSucc⟩) • E' := by
    intro f' E'
    have open_i : ⊤ ≤ f' ⁻¹ᵁ standardOpen J S i := by
      rw [homOfSections_preimage_standardOpen, hi', T.basicOpen_one]
    let N := twistRestrict f' 1
    let D := f' ⁻¹ᵁ standardOpen J S i
    have restr (j : J) : N.presheaf.map (homOfLE open_i).op
        (N.presheaf.map (homOfLE (le_top : D ≤ ⊤)).op (pull f' (z j))) = pull f' (z j) :=
      (Scheme.Modules.presheaf_map_map_apply _ _ _).trans (Scheme.Modules.presheaf_map_id_apply _ _)
    have gen' : IsFreeGenerator E' := by
      change IsFreeGenerator (pull f' (z i))
      rw [← restr i]
      exact (isFreeGenerator_pullbackSection_twistOneSection f' i).map open_i
    have coord' (j : J) : pull f' (z j) = s' j • E' := by
      have H := congrArg (N.presheaf.map (homOfLE open_i).op)
        (pullbackSection_twistOneSection_map_eq_smul f' j i)
      rw [Scheme.Modules.map_smul] at H
      have eqn : pull f' (z j) =
          f'.appLE (standardOpen J S i) ⊤ open_i (coordRatio J S i j) • E' :=
        (restr j).symm.trans (H.trans (congrArg (_ • ·) (restr i)))
      rwa [homOfSections_appLE_coordRatio π' s' hs' hi'] at eqn
    have H := eval_lam f' s' E' coord'
    rw [show f' ≫ P ↘ S = π' from homOfSections_over ..] at H
    exact ⟨gen', coord', H⟩
  obtain ⟨genX, -, valX⟩ := on_tuple π s hs hi
  have hpre : f ⁻¹ᵁ B = V :=
    preimage_zeroLocus_openComplement_eq_basicOpen f lam genX (by rw [hp]; exact valX)
  refine ⟨hpre, ?_⟩
  let lift := f.resLE B V hpre.ge
  have liftfac : lift ≫ B.ι = V.ι ≫ f := Scheme.Hom.resLE_comp_ι _ _
  let s' (j : J) := V.ι.appTop (s j)
  have hs' := span_range_appTop_eq_top V.ι hs
  have hi' : s' i = 1 := by simp [s', hi]
  let f' := homOfSections (V.ι ≫ π) s' hs'
  have hcomp : V.ι ≫ f = f' := comp_homOfSections ..
  obtain ⟨genV, eqV, lamV⟩ := on_tuple (V.ι ≫ π) s' hs' hi'
  have hVal : pull f' lam = V.ι.appTop p • (pull f' (z i)) := by
    have val : V.ι.appTop p = s' ⟨Fin.last m⟩ +
        ∑ j, (V.ι ≫ π).appTop (l j) * s' ⟨j.castSucc⟩ := by
      calc
        _ = V.ι.appTop (s ⟨Fin.last m⟩ + ∑ j, π.appTop (l j) * s ⟨j.castSucc⟩) :=
          congrArg V.ι.appTop hp
        _ = _ := by
          simp only [map_add, map_sum, map_mul, Scheme.Hom.comp_appTop, CommRingCat.comp_apply, s']
    exact val.symm ▸ lamV
  have fac : lift ≫ h = g := by
    apply AffineSpace.hom_ext
    · rw [Category.assoc, hbase, ← Category.assoc, liftfac, Category.assoc, homOfSections_over,
        AffineSpace.homOfVector_over]
    · rintro ⟨j⟩
      rw [show g.appTop (AffineSpace.coord S ⟨j⟩) = X.divBasicOpen (s ⟨j.castSucc⟩) p from
        AffineSpace.homOfVector_appTop_coord ..]
      change (lift ≫ h).appTop (y j) = _
      rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, hcoord]
      apply X.eq_divBasicOpen
      apply genV.smul_left_injective
      have H := all_coord lift f' (liftfac.trans hcomp) ⟨j.castSucc⟩
      rw [hVal] at H
      exact (mul_smul _ _ _).trans (H.trans (eqV ⟨j.castSucc⟩))
  change g ≫ invChart ≫ B.ι = _
  rw [← fac, Category.assoc, ← Category.assoc h invChart, h_ki, Category.id_comp, liftfac]

end WeilII
