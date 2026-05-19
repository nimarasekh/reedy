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

abbrev MorphismProperty.identities (C : Type*) [Category* C] :
    MorphismProperty C :=
  .ofHoms (fun X ↦ 𝟙 X)

end CategoryTheory
