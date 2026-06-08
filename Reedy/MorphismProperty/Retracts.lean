/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.MorphismProperty.Retract

/-!
# Stability under retracts of an intersection of property of morphisms

-/

@[expose] public section

namespace CategoryTheory.MorphismProprerty

instance {C : Type*} [Category* C] {ι : Type*} (W : ι → MorphismProperty C)
    [∀ i, (W i).IsStableUnderRetracts] :
    (⨅ i, W i).IsStableUnderRetracts where
  of_retract h hf := by
    sorry

end CategoryTheory.MorphismProprerty
