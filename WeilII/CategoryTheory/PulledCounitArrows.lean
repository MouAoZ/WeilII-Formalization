module

public import WeilII.CategoryTheory.SupportMateArrow
public import WeilII.CategoryTheory.TransportCounitSquares
import WeilII.CategoryTheory.CounitBijectionIso

open CategoryTheory

namespace WeilII

/-- Compare two arrows by a pair of representing counits before and after base change.
The two composites over the new base must compute pullback of the old counits. -/
public theorem arrowIso_of_pulled_counits
    {C B D E : Type*} [Category* C] [Category* B] [Category* D] [Category* E]
    {I : C ⥤ B} {J : D ⥤ E} (ff : J.FullyFaithful) (P : B ⥤ E)
    {A A' B₁ B₂ : D} (f : A ⟶ B₁) (g : A' ⟶ B₂)
    {S S' : C} {X Y : B} {T T' : E} (c : I.obj S ⟶ X) (d : I.obj S' ⟶ Y)
    (c' : J.obj B₁ ⟶ T) (d' : J.obj B₂ ⟶ T') (x : X ≅ Y) (y : T ≅ T')
    {v : P.obj X ⟶ T} {v' : P.obj Y ⟶ T'} (h : v ≫ y.hom = P.map x.hom ≫ v')
    (hc : ∀ N, Function.Bijective (fun a : N ⟶ S ↦ I.map a ≫ c ≫ x.hom))
    (hd : ∀ N, Function.Bijective (fun a : N ⟶ S' ↦ I.map a ≫ d))
    (hc' : ∀ N, Function.Bijective (fun a : N ⟶ B₁ ↦ J.map a ≫ c' ≫ y.hom))
    (hd' : ∀ N, Function.Bijective (fun a : N ⟶ B₂ ↦ J.map a ≫ d'))
    (r : Nonempty (Over.mk (J.map f ≫ c') ≅ Over.mk (P.map c ≫ v)))
    (r' : Nonempty (Over.mk (J.map g ≫ d') ≅ Over.mk (P.map d ≫ v'))) :
    Nonempty (Arrow.mk f ≅ Arrow.mk g) := by
  obtain ⟨k, hk⟩ := iso_of_counit_bijections I (c ≫ x.hom) d hc hd
  obtain ⟨s⟩ := transport_overIso_of_counit_squares P (I.mapIso k) hk h r.some r'.some
  exact arrowIso_of_counit_bijections ff f g (c' ≫ y.hom) d' hc' hd' s

end WeilII
