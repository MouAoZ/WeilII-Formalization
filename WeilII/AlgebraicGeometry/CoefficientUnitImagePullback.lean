module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LisseLatticeEmbedding

/-! # Pullback of the image of the coefficient-extension unit -/

open AlgebraicGeometry AlgebraicGeometry.ProEtale CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.ProEtale.CondensedRing
open scoped CategoryTheory.Obj

namespace WeilII

universe u

/-- Given an identification of the pullback of a module with a local model, the pullback of the
image of its coefficient-extension unit is the image of the unit on the local model. -/
public theorem nonempty_upperStar_image_coefficientUnit_iso
    {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
    (a : Λ ⟶ Λ') [IsMonHom a] {X S : Scheme.{u}} (f : X ⟶ S)
    (N : Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1}) (condensedRingObj Λ S))
    {P : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)}
    (d : (f)^*⟦Λ⟧.obj N ≅ P) :
    Nonempty ((f)^*⟦Λ⟧.obj (image ((Mod.extendRestrictAdjunction (coefficientMap a S)).unit.app N)) ≅
      image ((Mod.extendRestrictAdjunction (coefficientMap a X)).unit.app P)) := by
  let G := (f)^*⟦Λ⟧
  let η := (Mod.extendRestrictAdjunction (coefficientMap a S)).unit.app N
  let η' := (Mod.extendRestrictAdjunction (coefficientMap a X)).unit.app (G.obj N)
  let e := (comapUpperStarIso a f).symm.app ((Mod.extendScalars (coefficientMap a S)).obj N) ≪≫
    (Mod.comap (coefficientMap a X)).mapIso ((pullIso a f).symm.app N)
  have h : G.map η ≫ e.hom = η' := by
    have h' := upperStar_map_unit_app_comp_comapUpperStarIso_inv_app a f N
    dsimp only [e, Iso.trans_hom, Iso.app_hom, Iso.symm_hom, Functor.mapIso_hom]
    rw [← Category.assoc, h', Category.assoc, ← Functor.map_comp]
    simp [η', G]
  have : StrongEpi (G.map (factorThruImage η)) := strongEpi_of_epi _
  let pullImage := image.isoStrongEpiMono (G.map (factorThruImage η)) (G.map (image.ι η) ≫ e.hom)
    (show G.map (factorThruImage η) ≫ G.map (image.ι η) ≫ e.hom = η' by
      rw [← Category.assoc, ← G.map_comp, image.fac, h])
  let adj := Mod.extendRestrictAdjunction (coefficientMap a X)
  let L := Mod.extendScalars (coefficientMap a X) ⋙ Mod.comap (coefficientMap a X)
  let chart := Arrow.isoMk' η' (adj.unit.app P) d (L.mapIso d) (adj.unit.naturality d.hom)
  exact ⟨pullImage ≪≫ im.mapIso chart⟩

end WeilII
