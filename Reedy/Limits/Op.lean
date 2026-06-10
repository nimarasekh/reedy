/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou, Lyne Moser
-/
module

public import Mathlib.CategoryTheory.Adjunction.Limits

/-!
# (Co)limits and the opposite of the opposite of a category

-/

@[expose] public section

namespace CategoryTheory.Limits

variable {J C : Type*} [Category* J] [Category* C]

instance [HasColimitsOfShape J C] : HasColimitsOfShape J Cᵒᵖᵒᵖ :=
  Adjunction.hasColimitsOfShape_of_equivalence (opOpEquivalence C).functor

instance [HasColimitsOfShape J C] : HasColimitsOfShape Jᵒᵖᵒᵖ C :=
  hasColimitsOfShape_of_equivalence (opOpEquivalence _).symm

instance [HasLimitsOfShape J C] : HasLimitsOfShape J Cᵒᵖᵒᵖ :=
  Adjunction.hasLimitsOfShape_of_equivalence (opOpEquivalence C).functor

instance [HasLimitsOfShape J C] : HasLimitsOfShape Jᵒᵖᵒᵖ C :=
  hasLimitsOfShape_of_equivalence (opOpEquivalence _).symm

end CategoryTheory.Limits
