/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Limits.Preserves.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Products

/-!
# `piConst` preserves limits

-/

@[expose] public section

universe v' u' w v u

namespace CategoryTheory.Limits

-- the dual result for `sigmaConst` is in `Mathlib.CategoryTheory.Limits.Preserves.SigmaConst`
instance {C : Type u} [Category.{v} C] [HasProducts.{w} C] (R : C) :
    PreservesLimitsOfSize.{v', u'} (piConst.{w}.obj R) :=
-- For a suitable value of the universe `w`, this would follow from
-- the fact that `piConst` is a right adjoint, but we want a more general proof
  sorry


end CategoryTheory.Limits
