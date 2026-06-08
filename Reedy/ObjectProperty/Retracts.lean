/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.ObjectProperty.Retract

/-!
# Stability under retracts of an inverse image of a property of objects

-/

@[expose] public section

namespace CategoryTheory.ObjectProperty

instance {C D : Type*} [Category* C] [Category* D] (P : ObjectProperty D) (F : C ⥤ D)
    [P.IsStableUnderRetracts] :
    (P.inverseImage F).IsStableUnderRetracts where
  of_retract h hX :=
    sorry

end CategoryTheory.ObjectProperty
