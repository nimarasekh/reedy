/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.MorphismProperty.Basic

/-!
# ...

-/

universe u

@[expose] public section

namespace CategoryTheory

namespace MorphismProperty

variable (C : Type*) [Category* C]

abbrev identities : MorphismProperty C :=
  .ofHoms (fun X ↦ 𝟙 X)

variable {C} in
lemma identities_op_iff {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    identities Cᵒᵖ f ↔ identities C f.unop :=
  sorry

end MorphismProperty

end CategoryTheory
