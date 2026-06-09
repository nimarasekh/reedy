/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Adjunction.Parametrized
public import Mathlib.CategoryTheory.Elements
public import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory

/-!
# Weighted colimits

-/

@[expose] public section

universe w v u

namespace CategoryTheory.Limits

open Opposite

-- See A.6 in Riehl-Verity (here, we do not need the enriched version)

variable {J : Type u} [Category.{v} J] {C : Type*} [Category* C]

abbrev WeightedCocone (P : Jᵒᵖ ⥤ Type w) (F : J ⥤ C) :=
  Cocone ((CategoryOfElements.π P).leftOp ⋙ F)

namespace WeightedCocone

variable {P : Jᵒᵖ ⥤ Type w} {F : J ⥤ C}

set_option backward.defeqAttrib.useBackward true in
@[simps pt]
def mk (pt : C) (ι : ∀ ⦃j : J⦄ (_ : P.obj (op j)), F.obj j ⟶ pt)
    (hι : ∀ ⦃j₁ j₂ : J⦄ (x : P.obj (op j₁)) (f : j₂ ⟶ j₁),
        F.map f ≫ ι x = ι (P.map f.op x)) :
    WeightedCocone P F where
  pt := pt
  ι.app x := ι x.unop.2
  ι.naturality x₁ x₂ f := by simpa using hι (x₂.unop.2) f.unop.1.unop

protected abbrev ι (c : WeightedCocone P F) {j : J} (x : P.obj (op j)) :
    F.obj j ⟶ c.pt :=
  (Cocone.ι c).app (op (Functor.elementsMk _ _ x))

protected abbrev IsColimit (c : WeightedCocone P F) := Limits.IsColimit c

namespace IsColimit

variable {c : WeightedCocone P F} (hc : c.IsColimit)
  {Z : C} (ι : ∀ ⦃j : J⦄ (_ : P.obj (op j)), F.obj j ⟶ Z)
  (hι : ∀ ⦃j₁ j₂ : J⦄ (x : P.obj (op j₁)) (f : j₂ ⟶ j₁),
    F.map f ≫ ι x = ι (P.map f.op x))

def desc : c.pt ⟶ Z :=
  Limits.IsColimit.desc hc (WeightedCocone.mk Z ι hι)

@[reassoc (attr := simp)]
lemma fac {j : J} (x : P.obj (op j)) :
    c.ι x ≫ hc.desc ι hι = ι x :=
  Limits.IsColimit.fac hc (WeightedCocone.mk Z ι hι) (op (Functor.elementsMk _ _ x))

end IsColimit

set_option backward.defeqAttrib.useBackward true in
@[simps]
protected def yoneda (F : J ⥤ C) (j : J) :
    WeightedCocone (yoneda.obj j) F where
  pt := F.obj j
  ι.app u := F.map u.unop.2
  ι.naturality _ _ f := by
    dsimp
    simp only [← Functor.map_comp, Category.comp_id]
    congr
    exact f.unop.2

def isColimitYoneda (F : J ⥤ C) (j : J) : (WeightedCocone.yoneda F j).IsColimit  := by
  -- use that the category of elements has an initial object
  sorry

end WeightedCocone

section

variable [HasColimitsOfSize.{v, max u w} C]

noncomputable def weightedColim : (Jᵒᵖ ⥤ Type w) ⥤ (J ⥤ C) ⥤ C where
  obj P := (Functor.whiskeringLeft _ _ _).obj (CategoryOfElements.π P).leftOp ⋙ colim
  map := sorry

noncomputable def weightedColimObjObjι
    (P : Jᵒᵖ ⥤ Type w) (F : J ⥤ C) ⦃j : J⦄ (x : P.obj (op j)) :
    F.obj j ⟶ (weightedColim.obj P).obj F :=
  colimit.ι ((CategoryOfElements.π P).leftOp ⋙ F) (op (Functor.elementsMk _ _ x))

@[simps]
noncomputable def weightedColimCocone (P : Jᵒᵖ ⥤ Type w) (F : J ⥤ C) :
    WeightedCocone P F where
  pt := (weightedColim.obj P).obj F
  ι.app x := weightedColimObjObjι P F x.unop.2
  ι.naturality := sorry

noncomputable def isColimitWeightedColimCocone (P : Jᵒᵖ ⥤ Type w) (F : J ⥤ C) :
    (weightedColimCocone P F).IsColimit  :=
  colimit.isColimit _

noncomputable def weightedColimitObjObjIsoOfIsColimit
    {P : Jᵒᵖ ⥤ Type w} {F : J ⥤ C} {c : WeightedCocone P F}
    (hc : c.IsColimit) :
    (weightedColim.obj P).obj F ≅ c.pt :=
  IsColimit.coconePointUniqueUpToIso (colimit.isColimit _) hc

instance (P : Jᵒᵖ ⥤ Type w) {K : Type*} [Category* K] [HasColimitsOfShape K C] :
    PreservesColimitsOfShape K (weightedColim.obj P : (J ⥤ C) ⥤ C) where
  preservesColimit {G} := by dsimp [weightedColim]; infer_instance

section

variable [HasProducts.{w} C]

-- hopefully, this is the expect parametrized right adjoint to `weightedColim`
@[simps]
noncomputable def weightedColimRightAdj : (Jᵒᵖ ⥤ Type w)ᵒᵖ ⥤ C ⥤ (J ⥤ C) where
  obj P := piConst.{w} ⋙ (Functor.whiskeringLeft ..).obj P.unop.rightOp
  map {P₁ P₂} f := Functor.whiskerLeft _ ((Functor.whiskeringLeft ..).map f.unop.rightOp)

set_option backward.defeqAttrib.useBackward true in
noncomputable def weightedColimHomEquiv (P : Jᵒᵖ ⥤ Type w) (F : J ⥤ C) (X : C) :
    ((weightedColim.obj P).obj F ⟶ X) ≃ (F ⟶ P.rightOp ⋙ piConst.obj X) where
  toFun x :=
    { app j := Pi.lift (fun y ↦ weightedColimObjObjι P F y ≫ x)
      naturality := sorry }
  invFun f :=
    (isColimitWeightedColimCocone P F).desc (fun j y ↦ f.app j ≫ Pi.π _ y) sorry
  left_inv := sorry
  right_inv := sorry

noncomputable def weightedColimitAdj₂ :
    weightedColim.{w} (J := J) (C := C) ⊣₂ weightedColimRightAdj where
  adj P :=
    Adjunction.mkOfHomEquiv
      { homEquiv := weightedColimHomEquiv _
        homEquiv_naturality_left_symm := sorry
        homEquiv_naturality_right := sorry }
  unit_whiskerRight_map := sorry

instance (F : J ⥤ C) {K : Type*} [Category* K] [HasColimitsOfShape K (Type w)] :
    PreservesColimitsOfShape K (weightedColim.flip.obj F : (Jᵒᵖ ⥤ Type w) ⥤ C) := by
  -- strategy: show that `weightedColim` is a left bifunctor in a parametrized
  -- adjunction and dualize the result in `CategoryTheory.Adjunction.ParametrizedLimits`
  sorry

end

-- A.6 (iv)
@[simps!]
noncomputable def weightedColim₂ {J' : Type*} [Category* J'] :
    (J' ⥤ Jᵒᵖ ⥤ Type w) ⥤ (J ⥤ C) ⥤ (J' ⥤ C) :=
  (weightedColim.{w}.flip ⋙ Functor.whiskeringRight _ _ _).flip

-- show that `weightedColim₂` also preserves colimits in both variables

end

variable (J C) in
def weightedColim₂ObjYonedaIso [HasColimitsOfSize.{v, max u v} C] :
    weightedColim₂.obj yoneda ≅ 𝟭 (J ⥤ C) :=
  sorry

end CategoryTheory.Limits
