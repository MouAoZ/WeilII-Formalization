module

public import WeilConjectures.WeilSheaf.GeometricFiberPullbackTraceFunction

/-! # Presentations of an invariant adic sheaf by pullback from a model -/

@[expose] public section

open AlgebraicGeometry CategoryTheory AlgebraicGeometry.ProEtale

namespace WeilII

universe u

variable {ℓ : ℕ} [Fact ℓ.Prime] {X Z : Scheme.{u}}

/-- Compatibility of a map from the canonical inverse image with the two structure maps. -/
def AdicInvariantMap {A : Type*} [Category.{u+1} A] [Abelian A] [IsGrothendieckAbelian.{u+1} A]
    (p : Z ⟶ X) {a : Z ⟶ Z} (ha : a ≫ p = p) (E : Sheaf (Scheme.ProEt.topology X) A)
    {M : Sheaf (Scheme.ProEt.topology Z) A} (σ : (a)^*[A].obj M ⟶ M)
    (v : (p)^*[A].obj E ⟶ M) : Prop :=
  (upperStarFactor A ha).hom.app E ≫ (a)^*[A].map v ≫ σ = v

/-- A presentation of a sheaf with structure map σ as the pullback of E along p.
The factorization a ≫ p = p gives the canonical structure map on this pullback. -/
structure AdicInvariantPresentation (p : Z ⟶ X) {a : Z ⟶ Z} (ha : a ≫ p = p)
    (E : AdicSheaf ℓ X) (M : AdicSheaf ℓ Z)
    (σ : (a)^*[WeilCoefficients.{u} ℓ].obj M.X ⟶ M.X) where
  iso : (p)^*ᵃ[ℓ].obj E ≅ M
  map : (p)^*[WeilCoefficients.{u} ℓ].obj E.X ⟶ M.X
  iso_hom : iso.hom.hom = map
  comm : AdicInvariantMap p ha E.X σ map

namespace AdicInvariantPresentation

variable {p : Z ⟶ X} {a : Z ⟶ Z} {ha : a ≫ p = p}
  {E : AdicSheaf ℓ X} {M : AdicSheaf ℓ Z} {σ : (a)^*[WeilCoefficients.{u} ℓ].obj M.X ⟶ M.X}

/-- Split pullback along a specified factorization, in the adic category. -/
noncomputable def factor {W : Scheme.{u}} {j : W ⟶ Z} {q : W ⟶ X} (h : j ≫ p = q)
    (E : AdicSheaf ℓ X) : (q)^*ᵃ[ℓ].obj E ≅ (j)^*ᵃ[ℓ].obj ((p)^*ᵃ[ℓ].obj E) :=
  ((adicUpperStarCongr ℓ h.symm) ≪≫ adicUpperStarComp ℓ j p).app E

theorem factor_hom {W : Scheme.{u}} {j : W ⟶ Z} {q : W ⟶ X} (h : j ≫ p = q)
    (E : AdicSheaf ℓ X) :
    (factor h E).hom.hom = (upperStarFactor _ h).hom.app E.X := by
  subst q
  simp only [factor, upperStarFactor, Iso.app_hom, Iso.trans_hom, NatTrans.comp_app, Mod.comp_hom',
    adicUpperStarCongr_hom_app_hom, adicUpperStarComp_hom_app_hom]
  rfl

theorem paste {C D : Type*} [Category* C] [Category* D]
    (A : C ⥤ C) (B : D ⥤ D) (J L : C ⥤ D) (α : L ⟶ J ⋙ B) (β : L ⟶ A ⋙ J)
    {U M : C} {V N : D} (k : U ⟶ A.obj U) (s : V ⟶ B.obj V) (t : V ⟶ J.obj U)
    (u : V ⟶ L.obj U) (v : U ⟶ M) (z : J.obj M ⟶ N)
    (σ : A.obj M ⟶ M) (τ : B.obj N ⟶ N)
    (h₁ : s ≫ B.map t = u ≫ α.app U) (h₂ : t ≫ J.map k = u ≫ β.app U)
    (hv : k ≫ A.map v ≫ σ = v)
    (hz : α.app M ≫ B.map z ≫ τ = β.app M ≫ J.map σ ≫ z) :
    s ≫ B.map (t ≫ J.map v ≫ z) ≫ τ = t ≫ J.map v ≫ z := by
  have n₁ := α.naturality v
  have n₂ := β.naturality v
  simp only [Functor.comp_map] at n₁ n₂
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% h₁, ← reassoc_of% n₁, hz, reassoc_of% n₂, ← reassoc_of% h₂,
    ← J.map_comp_assoc (A.map v) σ, ← J.map_comp_assoc, hv]

/-- A morphism intertwines two structure maps through the two comparisons from L. -/
def Intertwines {C D : Type*} [Category* C] [Category* D] (A : C ⥤ C) (B : D ⥤ D) (J L : C ⥤ D)
    (α : L ≅ J ⋙ B) (β : L ≅ A ⋙ J) {M : C} {N : D}
    (σ : A.obj M ⟶ M) (τ : B.obj N ⟶ N) (z : J.obj M ⟶ N) : Prop :=
  α.hom.app M ≫ B.map z ≫ τ = β.hom.app M ≫ J.map σ ≫ z

/-- The map on sheaves from a factored pullback to its chosen presentation. -/
noncomputable def pullMap {A : Type*} [Category.{u+1} A] [Abelian A] [IsGrothendieckAbelian.{u+1} A]
    {W : Scheme.{u}} {j : W ⟶ Z} {q : W ⟶ X} (hj : j ≫ p = q)
    (E : Sheaf (Scheme.ProEt.topology X) A) {M : Sheaf (Scheme.ProEt.topology Z) A}
    {N : Sheaf (Scheme.ProEt.topology W) A} (v : (p)^*[A].obj E ⟶ M)
    (z : (j)^*[A].obj M ⟶ N) : (q)^*[A].obj E ⟶ N :=
  (upperStarFactor A hj).hom.app E ≫ (j)^*[A].map v ≫ z

theorem paste_factors {A : Type*} [Category.{u+1} A] [Abelian A]
    [IsGrothendieckAbelian.{u+1} A] {X Z W : Scheme.{u}}
    {p : Z ⟶ X} {a : Z ⟶ Z} (ha : a ≫ p = p) (j : W ⟶ Z) {q : W ⟶ X}
    (hj : j ≫ p = q) {b : W ⟶ W} (hb : b ≫ q = q) (sq : b ≫ j = j ≫ a)
    (E : Sheaf (Scheme.ProEt.topology X) A) {M : Sheaf (Scheme.ProEt.topology Z) A}
    {N : Sheaf (Scheme.ProEt.topology W) A} {σ : (a)^*[A].obj M ⟶ M}
    {τ : (b)^*[A].obj N ⟶ N} (v : (p)^*[A].obj E ⟶ M) (z : (j)^*[A].obj M ⟶ N)
    (hv : AdicInvariantMap p ha E σ v)
    (hz : Intertwines (a)^*[A] (b)^*[A] (j)^*[A] (b ≫ j)^*[A]
      (upperStarFactor A (rfl : b ≫ j = b ≫ j)) (upperStarFactor A sq.symm) σ τ z) :
    AdicInvariantMap q hb E τ (pullMap hj E v z) := by
  have hc : (b ≫ j) ≫ p = q := (Category.assoc _ _ _).trans ((congrArg (b ≫ ·) hj).trans hb)
  exact paste (a)^*[A] (b)^*[A] (j)^*[A] (b ≫ j)^*[A]
    (upperStarFactor A (rfl : b ≫ j = b ≫ j)).hom (upperStarFactor A sq.symm).hom
    ((upperStarFactor A ha).hom.app E) ((upperStarFactor A hb).hom.app E)
    ((upperStarFactor A hj).hom.app E) ((upperStarFactor A hc).hom.app E) v z σ τ
    (upperStarFactor_hom_app_assoc A hj hb rfl hc E)
    (upperStarFactor_hom_app_assoc A ha hj sq.symm hc E) hv hz

def RawSquare {C D : Type*} [Category* C] [Category* D] (A : C ⥤ C) (B : D ⥤ D)
    (J L L' : C ⥤ D) (α : L ≅ J ⋙ B) (i : L ≅ L') (β : L' ≅ A ⋙ J) {M : C} {N : D}
    (σ : A.obj M ⟶ M) (τ : B.obj N ⟶ N) (z : J.obj M ⟶ N) : Prop :=
  α.hom.app M ≫ B.map z ≫ τ = i.hom.app M ≫ β.hom.app M ≫ J.map σ ≫ z

theorem intertwines_of_raw {C D : Type*} [Category* C] [Category* D] (A : C ⥤ C) (B : D ⥤ D)
    (J L L' : C ⥤ D) (α α' : L ≅ J ⋙ B) (β : L ≅ A ⋙ J) (i : L ≅ L') (v : L' ≅ A ⋙ J)
    {M : C} {N : D} (σ : A.obj M ⟶ M) (τ : B.obj N ⟶ N) (z : J.obj M ⟶ N)
    (hα : α = α') (hβ : β = i ≪≫ v) (hz : RawSquare A B J L L' α' i v σ τ z) :
    Intertwines A B J L α β σ τ z := by
  unfold RawSquare at hz
  unfold Intertwines
  rw [hα, hβ, Iso.trans_hom, NatTrans.comp_app, Category.assoc]
  exact hz

def Square {A : Type*} [Category.{u+1} A] [Abelian A]
    [IsGrothendieckAbelian.{u+1} A] {Z W : Scheme.{u}}
    {a : Z ⟶ Z} (j : W ⟶ Z)
    {b : W ⟶ W} (sq : b ≫ j = j ≫ a)
    {M : Sheaf (Scheme.ProEt.topology Z) A}
    {N : Sheaf (Scheme.ProEt.topology W) A} (σ : (a)^*[A].obj M ⟶ M)
    (τ : (b)^*[A].obj N ⟶ N) (z : (j)^*[A].obj M ⟶ N) : Prop :=
  RawSquare (a)^*[A] (b)^*[A] (j)^*[A] (b ≫ j)^*[A] (j ≫ a)^*[A]
    (upperStarComp A b j) (upperStarCongr A sq) (upperStarComp A j a) σ τ z

theorem rawSquare_of_components {A : Type*} [Category.{u+1} A] [Abelian A]
    [IsGrothendieckAbelian.{u+1} A] {Z W : Scheme.{u}} {a : Z ⟶ Z} (j : W ⟶ Z)
    {b : W ⟶ W} (α : (b ≫ j)^*[A] ≅ (j)^*[A] ⋙ (b)^*[A])
    (i : (b ≫ j)^*[A] ≅ (j ≫ a)^*[A]) (β : (j ≫ a)^*[A] ≅ (a)^*[A] ⋙ (j)^*[A])
    {M : Sheaf (Scheme.ProEt.topology Z) A} {N : Sheaf (Scheme.ProEt.topology W) A}
    (σ : (a)^*[A].obj M ⟶ M) (τ : (b)^*[A].obj N ⟶ N) (z : (j)^*[A].obj M ⟶ N)
    (h : α.hom.app M ≫ (b)^*[A].map z ≫ τ =
      i.hom.app M ≫ β.hom.app M ≫ (j)^*[A].map σ ≫ z) :
    RawSquare (a)^*[A] (b)^*[A] (j)^*[A] (b ≫ j)^*[A] (j ≫ a)^*[A] α i β σ τ z := h

theorem square_of_components {A : Type*} [Category.{u+1} A] [Abelian A]
    [IsGrothendieckAbelian.{u+1} A] {Z W : Scheme.{u}}
    {a : Z ⟶ Z} (j : W ⟶ Z)
    {b : W ⟶ W} (sq : b ≫ j = j ≫ a)
    {M : Sheaf (Scheme.ProEt.topology Z) A}
    {N : Sheaf (Scheme.ProEt.topology W) A} (σ : (a)^*[A].obj M ⟶ M)
    (τ : (b)^*[A].obj N ⟶ N) (z : (j)^*[A].obj M ⟶ N)
    (h : (upperStarComp A b j).hom.app M ≫ (b)^*[A].map z ≫ τ =
      (upperStarCongr A sq).hom.app M ≫ (upperStarComp A j a).hom.app M ≫ (j)^*[A].map σ ≫ z) :
    Square j sq σ τ z :=
  rawSquare_of_components j (upperStarComp A b j) (upperStarCongr A sq) (upperStarComp A j a) σ τ z h

theorem square_of_other_instance {A : Type*} [Category.{u+1} A] [Abelian A]
    [_base : IsGrothendieckAbelian.{u+1} A] (other : IsGrothendieckAbelian.{u+1} A) {Z W : Scheme.{u}}
    {a : Z ⟶ Z} (j : W ⟶ Z)
    {b : W ⟶ W} (sq : b ≫ j = j ≫ a)
    {M : Sheaf (Scheme.ProEt.topology Z) A}
    {N : Sheaf (Scheme.ProEt.topology W) A} (σ : (a)^*[A].obj M ⟶ M)
    (τ : (b)^*[A].obj N ⟶ N) (z : (j)^*[A].obj M ⟶ N)
    (h : letI := other
      (upperStarComp A b j).hom.app M ≫ (b)^*[A].map z ≫ τ =
      (upperStarCongr A sq).hom.app M ≫ (upperStarComp A j a).hom.app M ≫ (j)^*[A].map σ ≫ z) :
    Square j sq σ τ z := by
  obtain rfl : other = _base := Subsingleton.elim _ _
  exact square_of_components j sq σ τ z h

theorem square_factors {A : Type*} [Category.{u+1} A] [Abelian A]
    [IsGrothendieckAbelian.{u+1} A] {Z W : Scheme.{u}}
    {a : Z ⟶ Z} (j : W ⟶ Z)
    {b : W ⟶ W} (sq : b ≫ j = j ≫ a)
    {M : Sheaf (Scheme.ProEt.topology Z) A}
    {N : Sheaf (Scheme.ProEt.topology W) A} {σ : (a)^*[A].obj M ⟶ M}
    {τ : (b)^*[A].obj N ⟶ N} (z : (j)^*[A].obj M ⟶ N)
    (hz : Square j sq σ τ z) :
    Intertwines (a)^*[A] (b)^*[A] (j)^*[A] (b ≫ j)^*[A]
      (upperStarFactor A (rfl : b ≫ j = b ≫ j)) (upperStarFactor A sq.symm) σ τ z :=
  intertwines_of_raw _ _ _ _ _ _ _ _ _ _ σ τ z (upperStarFactor_rfl A b j) rfl hz

noncomputable def pullIso {W : Scheme.{u}} {j : W ⟶ Z} {q : W ⟶ X} (hj : j ≫ p = q)
    (E : AdicSheaf ℓ X) {M : AdicSheaf ℓ Z} {N : AdicSheaf ℓ W}
    (v : (p)^*ᵃ[ℓ].obj E ≅ M) (z : (j)^*ᵃ[ℓ].obj M ≅ N) : (q)^*ᵃ[ℓ].obj E ≅ N :=
  factor hj E ≪≫ (j)^*ᵃ[ℓ].mapIso v ≪≫ z

theorem pullIso_hom {W : Scheme.{u}} {j : W ⟶ Z} {q : W ⟶ X} (hj : j ≫ p = q)
    (E : AdicSheaf ℓ X) {M : AdicSheaf ℓ Z} {N : AdicSheaf ℓ W}
    (v : (p)^*ᵃ[ℓ].obj E ≅ M) (w : (j)^*ᵃ[ℓ].obj M ≅ N)
    (v' : (p)^*[WeilCoefficients.{u} ℓ].obj E.X ⟶ M.X)
    (w' : (j)^*[WeilCoefficients.{u} ℓ].obj M.X ⟶ N.X) (hv : v.hom.hom = v') (hw : w.hom.hom = w') :
    (pullIso hj E v w).hom.hom = pullMap hj E.X v' w' := by
  subst v' w'
  exact congrArg₂ (· ≫ ·) (factor_hom hj E) (congrArg (· ≫ w.hom.hom) (adicUpperStar_map_hom j v.hom))

/-- Pull back an invariant presentation along an intertwining square. The coefficient
isomorphism ψ identifies the geometric pullback with the chosen sheaf on the new space. -/
noncomputable def pull (P : AdicInvariantPresentation p ha E M σ)
    {W : Scheme.{u}} (j : W ⟶ Z) {q : W ⟶ X} (hj : j ≫ p = q)
    {b : W ⟶ W} (hb : b ≫ q = q) (sq : b ≫ j = j ≫ a)
    {N : AdicSheaf ℓ W} {τ : (b)^*[WeilCoefficients.{u} ℓ].obj N.X ⟶ N.X}
    (ψ : (j)^*ᵃ[ℓ].obj M ≅ N)
    (z : (j)^*[WeilCoefficients.{u} ℓ].obj M.X ⟶ N.X) (hz : ψ.hom.hom = z)
    (hψ : Square j sq σ τ z) : AdicInvariantPresentation q hb E N τ where
  iso := pullIso hj E P.iso ψ
  map := pullMap hj E.X P.map z
  iso_hom := pullIso_hom hj E P.iso ψ P.map z P.iso_hom hz
  comm := paste_factors (A := WeilCoefficients.{u} ℓ) (M := M.X) (N := N.X) (σ := σ) (τ := τ)
    ha j hj hb sq E.X P.map z P.comm (square_factors (σ := σ) (τ := τ) j sq z hψ)

noncomputable def compModelMap {A : Type*} [Category.{u+1} A] [Abelian A] [IsGrothendieckAbelian.{u+1} A]
    {Y : Scheme.{u}} {f : X ⟶ Y} {q : Z ⟶ Y} (hq : p ≫ f = q)
    (H : Sheaf (Scheme.ProEt.topology Y) A) {M : Sheaf (Scheme.ProEt.topology Z) A}
    (v : (p)^*[A].obj ((f)^*[A].obj H) ⟶ M) : (q)^*[A].obj H ⟶ M :=
  (upperStarFactor A hq).hom.app H ≫ v

theorem comp_model_comm {A : Type*} [Category.{u+1} A] [Abelian A] [IsGrothendieckAbelian.{u+1} A]
    {Y : Scheme.{u}} (f : X ⟶ Y) (H : Sheaf (Scheme.ProEt.topology Y) A)
    {S : Sheaf (Scheme.ProEt.topology Z) A} {s : (a)^*[A].obj S ⟶ S}
    {q : Z ⟶ Y} (hq : p ≫ f = q) (hq' : a ≫ q = q)
    (v : (p)^*[A].obj ((f)^*[A].obj H) ⟶ S)
    (hv : AdicInvariantMap p ha ((f)^*[A].obj H) s v) :
    AdicInvariantMap q hq' H s (compModelMap hq H v) := by
  unfold AdicInvariantMap at hv ⊢
  unfold compModelMap
  rw [Functor.map_comp, Category.assoc,
    reassoc_of% upperStarFactor_hom_app_assoc A hq hq' ha hq H, hv]

noncomputable def compModelIso {Y : Scheme.{u}} {f : X ⟶ Y} {q : Z ⟶ Y}
    (hq : p ≫ f = q) (H : AdicSheaf ℓ Y) {M : AdicSheaf ℓ Z}
    (v : (p)^*ᵃ[ℓ].obj ((f)^*ᵃ[ℓ].obj H) ≅ M) : (q)^*ᵃ[ℓ].obj H ≅ M :=
  factor hq H ≪≫ v

theorem compModelIso_hom {Y : Scheme.{u}} {f : X ⟶ Y} {q : Z ⟶ Y}
    (hq : p ≫ f = q) (H : AdicSheaf ℓ Y) {M : AdicSheaf ℓ Z}
    (v : (p)^*ᵃ[ℓ].obj ((f)^*ᵃ[ℓ].obj H) ≅ M)
    (w : (p)^*[WeilCoefficients.{u} ℓ].obj ((f)^*[_].obj H.X) ⟶ M.X) (h : v.hom.hom = w) :
    (compModelIso hq H v).hom.hom = compModelMap hq H.X w := by
  subst w
  exact congrArg (· ≫ v.hom.hom) (factor_hom hq H)

/-- Compose the arithmetic map of an invariant presentation with the map from which its
coefficient sheaf was pulled back. -/
noncomputable def compModel {Y : Scheme.{u}} (f : X ⟶ Y) (H : AdicSheaf ℓ Y)
    (P : AdicInvariantPresentation p ha ((f)^*ᵃ[ℓ].obj H) M σ) {q : Z ⟶ Y}
    (hq : p ≫ f = q) (hq' : a ≫ q = q) : AdicInvariantPresentation q hq' H M σ where
  iso := compModelIso hq H P.iso
  map := compModelMap hq H.X P.map
  iso_hom := compModelIso_hom hq H P.iso P.map P.iso_hom
  comm := comp_model_comm (S := M.X) (s := σ) (ha := ha) f H.X hq hq' P.map P.comm

section Model

variable {k : Type u} [Field k] [Finite k] [Fact (ringChar k ≠ ℓ)]
variable {Y : Scheme.{u}} [Y.Over (Spec (CommRingCat.of k))]
local notation "π" => Scheme.Hom.geometricFiberProj (Y ↘ Spec (CommRingCat.of k))
local notation "Fr" => Scheme.Hom.geometricGaloisFrobenius (Y ↘ Spec (CommRingCat.of k))
variable {H : AdicSheaf ℓ Y} (hH : IsAdicLisseSheaf H)

theorem factor_comp_inv {A : Type*} [Category.{u+1} A] [Abelian A] [IsGrothendieckAbelian.{u+1} A]
    {X Y Z : Scheme.{u}} {a : Z ⟶ Y} {p : Y ⟶ X} {q : Z ⟶ X} (h : a ≫ p = q)
    (E : Sheaf (Scheme.ProEt.topology X) A) :
    (upperStarFactor A h).hom.app E ≫
      (upperStarComp A a p).inv.app E ≫ (upperStarCongr A h).hom.app E = 𝟙 _ := by
  subst q
  simp [upperStarFactor_rfl, upperStarCongr]

theorem factor_invariant {A : Type*} [Category.{u+1} A] [Abelian A] [IsGrothendieckAbelian.{u+1} A]
    {a : Z ⟶ Z} {p : Z ⟶ X} (h : a ≫ p = p) (E : Sheaf (Scheme.ProEt.topology X) A) :
    (upperStarFactor A h).hom.app E ≫ upperStarInvariantHom A p h E = 𝟙 _ := by
  unfold upperStarInvariantHom
  exact factor_comp_inv h E

theorem reverse_comm {C : Type*} [Category* C] (L : C ⥤ C)
    {M U : C} (e : M ≅ U) (σ : L.obj M ⟶ M) (s : U ⟶ L.obj U) (t : L.obj U ⟶ U)
    (h : σ ≫ e.hom = L.map e.hom ≫ t) (hst : s ≫ t = 𝟙 U) :
    s ≫ L.map e.inv ≫ σ = e.inv := by
  apply (cancel_mono e.hom).mp
  rw [Category.assoc, Category.assoc, h, ← Functor.map_comp_assoc, e.inv_hom_id,
    CategoryTheory.Functor.map_id, Category.id_comp, hst]

theorem invariant_of_iso {A : Type*} [Category.{u+1} A] [Abelian A] [IsGrothendieckAbelian.{u+1} A]
    (p : Z ⟶ X) {a : Z ⟶ Z} (ha : a ≫ p = p) (E : Sheaf (Scheme.ProEt.topology X) A)
    {M : Sheaf (Scheme.ProEt.topology Z) A} (σ : (a)^*[A].obj M ⟶ M) (e : M ≅ (p)^*[A].obj E)
    (h : σ ≫ e.hom = (a)^*[A].map e.hom ≫ upperStarInvariantHom A p ha E) :
    AdicInvariantMap p ha E σ e.inv :=
  reverse_comm (a)^*[A] e σ ((upperStarFactor A ha).hom.app E) (upperStarInvariantHom A p ha E)
    h (factor_invariant ha E)

noncomputable def ofInvariantIso {p : Z ⟶ X} {a : Z ⟶ Z} (ha : a ≫ p = p)
    {E : AdicSheaf ℓ X} {M : AdicSheaf ℓ Z}
    {σ : (a)^*[WeilCoefficients.{u} ℓ].obj M.X ⟶ M.X}
    (e : M ≅ (p)^*ᵃ[ℓ].obj E)
    (h : σ ≫ ((AdicSheaf.forget _).mapIso e).hom =
      (a)^*[_].map ((AdicSheaf.forget _).mapIso e).hom ≫ upperStarInvariantHom _ p ha E.X) :
    AdicInvariantPresentation p ha E M σ where
  iso := e.symm
  map := ((AdicSheaf.forget _).mapIso e).inv
  iso_hom := rfl
  comm := invariant_of_iso p ha E.X σ ((AdicSheaf.forget _).mapIso e) h

/-- The canonical Weil structure on the geometric pullback is presented by the projection. -/
noncomputable def geometric :
    AdicInvariantPresentation π (Scheme.Hom.geometricGaloisFrobenius_hom_comp_geometricFiberProj _)
      H (WeilSheaf.geometricFiberPullback (k₀ := k) hH).obj.carrier
      (WeilSheaf.geometricFiberPullback (k₀ := k) hH).frobeniusStr :=
  ofInvariantIso _ (WeilSheaf.geometricFiberPullbackObjCarrierIso hH)
    (WeilSheaf.frobeniusStr_comp_forget_map_eq _ _
      (WeilSheaf.geometricFiberPullback_str_hom_comp_carrierIso_hom hH))

/-- The same presentation for any positive power of geometric Frobenius. -/
noncomputable def geometricPow (d : ℕ) (hd : 1 ≤ d) :
    AdicInvariantPresentation π
      (Scheme.Hom.geometricGaloisFrobenius_pow_hom_comp_geometricFiberProj _ d)
      H (WeilSheaf.geometricFiberPullback (k₀ := k) hH).obj.carrier
      ((WeilSheaf.geometricFiberPullback (k₀ := k) hH).frobeniusPowStr d) :=
  ofInvariantIso _ (WeilSheaf.geometricFiberPullbackObjCarrierIso hH)
    (WeilSheaf.frobeniusPowStr_comp_eq_of_iso _ _
      (WeilSheaf.frobeniusStr_comp_forget_map_eq _ _
        (WeilSheaf.geometricFiberPullback_str_hom_comp_carrierIso_hom hH)) d hd)

theorem compare_presentations {C : Type*} [Category* C] (L : C ⥤ C)
    {B F G : C} (v : B ≅ F) (w : B ≅ G) {i : F ⟶ G} (hi : v.hom ≫ i = w.hom)
    {σ : L.obj F ⟶ F} {τ : L.obj G ⟶ G} (k : B ≅ L.obj B)
    (hv : k.hom ≫ L.map v.hom ≫ σ = v.hom) (hw : k.hom ≫ L.map w.hom ≫ τ = w.hom) :
    L.map i ≫ τ = σ ≫ i := by
  apply (cancel_epi (k.hom ≫ L.map v.hom)).mp
  simp only [Category.assoc]
  rw [← L.map_comp_assoc, hi, hw, reassoc_of% hv, hi]

/-- Two presentations over the same arithmetic map identify the Weil sheaves. -/
noncomputable def weilIso {B : Scheme.{u}} {p : (Y ↘ Spec (CommRingCat.of k)).geometricFiber ⟶ B}
    {hp : (Fr).asIso.hom ≫ p = p} {E : AdicSheaf ℓ B} {F G : WeilSheaf k ℓ Y}
    (P : AdicInvariantPresentation p hp E F.obj.carrier F.frobeniusStr)
    (Q : AdicInvariantPresentation p hp E G.obj.carrier G.frobeniusStr) : F ≅ G := by
  let e := P.iso.symm ≪≫ Q.iso
  have he : P.iso.hom.hom ≫ e.hom.hom = Q.iso.hom.hom := by
    rw [← Mod.comp_hom']
    exact congrArg Mod.Hom.hom (P.iso.hom_inv_id_assoc _)
  let a := (Fr).asIso
  have w : (a.hom)^*[WeilCoefficients.{u} ℓ].map e.hom.hom ≫ G.frobeniusStr = F.frobeniusStr ≫ e.hom.hom := by
    have hp₁ := P.comm
    have hq := Q.comm
    unfold AdicInvariantMap at hp₁ hq
    rw [← P.iso_hom] at hp₁
    rw [← Q.iso_hom] at hq
    exact compare_presentations _ ((AdicSheaf.forget _).mapIso P.iso)
      ((AdicSheaf.forget _).mapIso Q.iso) he ((upperStarFactor _ hp).app E.X) hp₁ hq
  refine ObjectProperty.isoMk _ (Endofunctor.IsoAlgebra.isoMk e ?_)
  apply Mod.hom_ext
  change ((a.inv)_*ᵃ[ℓ].map e.hom ≫ G.obj.str.hom).hom = (F.obj.str.hom ≫ e.hom).hom
  rw [Mod.comp_hom', Mod.comp_hom', adicLowerStar_map_hom]
  apply (cancel_epi ((upperStarIsoLowerStarInv (WeilCoefficients.{u} ℓ) a).hom.app F.obj.carrier.X)).mp
  have n := (upperStarIsoLowerStarInv (WeilCoefficients.{u} ℓ) a).hom.naturality e.hom.hom
  exact ((reassoc_of% n) G.obj.str.hom.hom).symm.trans (w.trans (Category.assoc _ _ _))

end Model

end AdicInvariantPresentation

end WeilII
