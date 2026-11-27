module

public import WeilII.Paper.ChainGraphHyperplaneComplementFactorization
public import WeilII.Paper.ProjectiveHyperplaneIncidenceFamily
public import WeilConjectures.Compactification.Defs
import Mathlib.Logic.Equiv.Fin.Rotate
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Canonical
import WeilII.Paper.NormalizedHyperplaneFiberComplement
import WeilII.Paper.NormalizedHyperplaneParameterOpen

/-! # Compactifying chain graphs at points of the incidence parameter chart -/

namespace WeilII

open AlgebraicGeometry CategoryTheory ProjectiveSpace Scheme.Modules

universe u

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- For the fixed graph of the chain quadratic, every dense open of hyperplane parameters
contains a principal family of sections whose restricted graphs have affine compactifications
of dimension at most `n` (Zhang, Construction 2.5 and Katz A.1, A.6).
Use the normalized chart with coordinate order `(c,a,1)`. The chart ratios identify the
incidence fiber with the linear section in the graph factorization. Its inverse image is
the basic open of the chain polynomial. Transport the open and closed immersions of that
factorization along the two chart isomorphisms to compactify the actual restriction. -/
public theorem exists_chainGraph_incidenceCompactification
    (K : Type u) [Field K] (n : ℕ) (hn : 2 ≤ n) :
    let S := Spec (.of K)
    let X := 𝔸(ULift.{u} (Fin n); S)
    let J := ULift.{u} (Fin (n + 2))
    let P := ℙ(J; S)
    letI : S.Over S := ⟨𝟙 S⟩
    ∃ (f : X ⟶ P), f.IsOver S ∧ ∀ W : P.Opens, Dense (W : Set P) →
      ∃ g : MvPolynomial (Fin (n + 1)) K, g ≠ 0 ∧
        ∀ (a : Fin n → K) (c : K), MvPolynomial.eval (Fin.snoc a c) g ≠ 0 →
          ∃ (H : S ⟶ P) (hH : H.IsOver S), H (IsLocalRing.closedPoint K) ∈ W ∧
            letI := hH
            let B := (projectiveHyperplaneFiber H).subschemeι.openComplement
            let coeff := ((Scheme.ΓSpecIso (.of K)).inv ≫ (X ↘ S).appTop).hom
            let p := MvPolynomial.eval₂Hom coeff
              (fun i : Fin n ↦ AffineSpace.coord S (ULift.up.{u} i)) (chainSectionPolynomial a c)
            f ⁻¹ᵁ B = (X.zeroLocusSubschemeι {p}).openComplement ∧
              ∃ C : Compactification (morphismRestrict f B), IsAffine C.Z ∧
                topologicalKrullDim C.Z ≤ (n : WithBot ℕ∞) := by
  classical
  intro S X J P
  let : S.Over S := ⟨𝟙 S⟩
  let x (i : Fin n) := AffineSpace.coord S (ULift.up.{u} i)
  let coeff := ((Scheme.ΓSpecIso (.of K)).inv ≫ (X ↘ S).appTop).hom
  let ev := MvPolynomial.eval₂Hom coeff x
  let Q := chainSectionPolynomial (0 : Fin n → K) 0
  let tuple : Fin (n + 2) → Γ(X, ⊤) := Fin.cons 1 (Fin.snoc x (ev Q))
  let w (j : J) := tuple j.down
  have hw : Ideal.span (Set.range w) = ⊤ :=
    (Ideal.eq_top_iff_one _).mpr (Ideal.subset_span ⟨⟨0⟩, by simp [w, tuple]⟩)
  let f := homOfSections (X ↘ S) w hw
  refine ⟨f, ⟨homOfSections_over ..⟩, ?_⟩
  intro W hW
  let d : J := ⟨Fin.last (n + 1)⟩
  let idx : {j : J // j ≠ d} ≃ Fin (n + 1) :=
    { toFun := fun j ↦ j.1.down.castPred (fun h ↦ j.2 (ULift.ext h))
      invFun := fun j ↦ ⟨⟨j.castSucc⟩, fun h ↦ Fin.castSucc_ne_last _ (congrArg ULift.down h)⟩
      left_inv := fun j ↦ Subtype.ext (ULift.ext (Fin.castSucc_castPred _ _))
      right_inv := fun j ↦ Fin.castPred_castSucc _ }
  let perm := idx.trans (finRotate (n + 1)).symm
  obtain ⟨g, hg, points⟩ := exists_basicOpen_normalizedProjectiveParameters K J d perm W hW
  refine ⟨g, hg, ?_⟩
  intro a c hac
  obtain ⟨H, hH, hHW, hD, hr⟩ := points (Fin.snoc a c) hac
  have ho : H.IsOver S := ⟨hH⟩
  refine ⟨H, ho, hHW, ?_⟩
  let z := twistOneSection J S
  let scalar := ((Scheme.ΓSpecIso (.of K)).inv ≫ (P ↘ S).appTop).hom
  let lam := z d + (∑ i : Fin n, scalar (a i) • z ⟨i.succ.castSucc⟩) + scalar c • z ⟨0⟩
  let params : Fin (n + 2) → K := Fin.snoc (Fin.cons c a) 1
  let l (j : J) := (Scheme.ΓSpecIso (.of K)).inv (params j.down)
  have hl (j : J) : H.appLE _ ⊤ hD (coordRatio J S d j) = l j := by
    rcases j with ⟨j⟩
    induction j using Fin.lastCases with
    | last => simp [d, coordRatio_self, l, params]
    | cast j =>
      let t : {i : J // i ≠ d} := ⟨⟨j.castSucc⟩, fun h ↦ Fin.castSucc_ne_last j (congrArg ULift.down h)⟩
      rw [hr t]
      change (Scheme.ΓSpecIso (.of K)).inv (@Fin.snoc n (fun _ ↦ K) a c ((finRotate _).symm j)) = _
      simp only [Fin.snoc_eq_cons_rotate a c, Equiv.apply_symm_apply, l, params, Fin.snoc_castSucc]
  have sumLam : (∑ j : J, (P ↘ S).appTop (l j) • z j) = lam := by
    rw [← Equiv.ulift.symm.sum_comp]
    rw [Fin.sum_univ_castSucc, Fin.sum_univ_succ]
    simp only [Equiv.ulift_symm_apply, l, params, Fin.snoc_castSucc, Fin.snoc_last,
      Fin.cons_zero, Fin.cons_succ, map_one, one_smul]
    change scalar c • z ⟨0⟩ + (∑ i : Fin n, scalar (a i) • z ⟨i.succ.castSucc⟩) + z d = _
    dsimp only [lam]
    abel
  have hB := normalizedHyperplaneFiber_openComplement H d hD l hl
  dsimp only at hB
  rw [sumLam] at hB
  let p := ev (chainSectionPolynomial a c)
  let V := X.basicOpen p
  let B := (homOfGlobalSection _ lam).zeroLocus.subschemeι.openComplement
  change f ⁻¹ᵁ _ = (X.zeroLocusSubschemeι {p}).openComplement ∧ _
  rw [hB]
  obtain ⟨pre, aff, _, _, dim, chart, e, _, _, graph, fac⟩ :=
    chainGraph_hyperplaneComplement_factorization K n hn a c
  have hv : f ⁻¹ᵁ B = V := pre
  refine ⟨hv.trans ?_, ?_⟩
  · ext y
    change y ∈ V ↔ y ∉ Set.range (X.zeroLocusSubschemeι {p}).base
    rw [X.range_zeroLocusSubschemeι_singleton, Scheme.Opens.range_ι, Set.notMem_compl_iff]
    rfl
  · let u := X.isoOfEq hv
    have compactify {A Z : Scheme.{u}} {U : Z.Opens} {b : Z ⟶ A} [IsClosedImmersion b]
        {v : V.toScheme ⟶ A} (chart : B.toScheme ≅ A) (e : V.toScheme ≅ U.toScheme)
        (graph : v ≫ chart.inv ≫ B.ι = V.ι ≫ f) (fac : e.hom ≫ U.ι ≫ b = v)
        (aff : IsAffine Z) (dim : topologicalKrullDim Z ≤ (n : WithBot ℕ∞)) :
        ∃ C : Compactification (morphismRestrict f B), IsAffine C.Z ∧
          topologicalKrullDim C.Z ≤ (n : WithBot ℕ∞) := by
      let C : Compactification (morphismRestrict f B) :=
        { Z := Z
          i := u.hom ≫ e.hom ≫ U.ι
          g := b ≫ chart.inv
          comm := by
            apply (cancel_mono B.ι).mp
            simp only [Category.assoc, morphismRestrict_ι]
            rw [reassoc_of% fac, graph, ← Category.assoc, Scheme.isoOfEq_hom_ι]
          isProper := inferInstance
          isOpenImmersion := inferInstance }
      exact ⟨C, aff, dim⟩
    exact compactify chart e graph fac aff dim

end WeilII
