/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Reedy.WeightedLimits.Colimits

/-!
# Weighted limits

-/

@[expose] public section

universe w

namespace CategoryTheory.Limits

open Opposite

variable {J' : Type u} [Category.{v} J'] {C : Type*} [Category* C]
  {J : Type*} [Category J]

-- TODO: dualize the API from the `Colimits.lean` file and
-- obtain the parametrized adjunction

noncomputable def weightedLim : (J' ⥤ Type w)ᵒᵖ ⥤ (J' ⥤ C) ⥤ C := sorry

noncomputable def weightedLim₂ :
    (J' ⥤ Jᵒᵖ ⥤ Type w)ᵒᵖ ⥤ (J' ⥤ C) ⥤ (J ⥤ C) := by
  sorry

variable (C) in
noncomputable def weightedLimObjCoyonedaObjIso (j' : J') :
    weightedLim.obj (op (coyoneda.obj (op j'))) ≅ (evaluation J' C).obj j' :=
  sorry


variable [HasColimitsOfSize.{w} C]

def weightedLim₂Adj₂ :
    weightedColim₂.{w} (J := J) (J' := J') (C := C) ⊣₂ weightedLim₂ :=
  sorry

end CategoryTheory.Limits
