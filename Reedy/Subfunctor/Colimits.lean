/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Reedy.Subfunctor.SubfunctorTwo
public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.CategoryTheory.Limits.Preserves.Basic

/-!
# Commutation to filtered colimits

-/

universe w

@[expose] public section

namespace CategoryTheory.Subfunctor₂

open Limits

-- look at `Mathlib.AlgebraicTopology.SimplicialSet.SubcomplexEvaluation`
-- for a similar result
instance {C D J : Type*} [Category* C] [Category* D] [Category* J]
    [IsFilteredOrEmpty J] (F : C ⥤ D ⥤ Type w) :
    PreservesColimitsOfShape J (toFunctorFunctor F) := by
  sorry

end CategoryTheory.Subfunctor₂
