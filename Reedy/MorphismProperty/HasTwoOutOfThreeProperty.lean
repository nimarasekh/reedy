/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.MorphismProperty.Composition

/-!
# Two out of three for properties of functors

-/

universe u

@[expose] public section

namespace CategoryTheory

-- this should be done first separately for
-- `IsStableUnderComposition`, `HasOfPostcompProperty` and `HasOfPrecompProperty`
instance {C : Type*} [Category* C] (W : MorphismProperty C) (D : Type*) [Category* D]
    [W.HasTwoOutOfThreeProperty] : (W.functorCategory D).HasTwoOutOfThreeProperty where
  comp_mem _ _ hf hg _ := W.comp_mem _ _ (hf _) (hg _)
  of_postcomp _ _ hg hfg _ := MorphismProperty.of_postcomp _ _ _ (hg _) (hfg _)
  of_precomp _ _ hf hfg _ := MorphismProperty.of_precomp _ _ _ (hf _) (hfg _)

end CategoryTheory
