module

public import WeilConjectures.CategoryTheory.ExchangeFormalism.PushforwardBaseChange

namespace WeilII

open CategoryTheory

/-- In an exchange formalism, the ordinary base change of a horizontal composite
is invertible if both constituent base changes are invertible. This is the
horizontal pasting identity with its invertible pullback-composition comparisons. -/
public theorem isIso_pfBaseChange_paste_horiz {C : Type*} [Category* C] {O : MorphismProperty C}
    (F : ExchangeFormalism C O) {U₂ U₁ U₀ Z₂ Z₁ Z₀ : C}
    (a : U₂ ⟶ U₁) (b : U₁ ⟶ U₀) (l : U₂ ⟶ Z₂) (m : U₁ ⟶ Z₁) (r : U₀ ⟶ Z₀)
    (c : Z₂ ⟶ Z₁) (d : Z₁ ⟶ Z₀) (t : U₂ ⟶ U₀) (s : Z₂ ⟶ Z₀)
    (w₁ : a ≫ m = l ≫ c) (w₂ : b ≫ r = m ≫ d) (ht : a ≫ b = t) (hs : c ≫ d = s)
    (w : t ≫ r = l ≫ s) (h₁ : IsIso (F.pfBaseChange a l m c w₁))
    (h₂ : IsIso (F.pfBaseChange b m r d w₂)) : IsIso (F.pfBaseChange t l r s w) := by
  rw [F.pfBaseChange_paste_horiz a b l m r c d t s w₁ w₂ ht hs w]
  dsimp only [TwoSquare.whiskerLeft, TwoSquare.whiskerRight, TwoSquare.vComp]
  infer_instance

end WeilII
