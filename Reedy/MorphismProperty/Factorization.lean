/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.MorphismProperty.Factorization

/-!
# ...

-/

universe u

@[expose] public section

namespace CategoryTheory.MorphismProperty.MapFactorizationData

variable {C : Type*} [Category* C]

@[simps]
protected def unop {W₁ W₂ : MorphismProperty Cᵒᵖ} {X Y : Cᵒᵖ} {f : X ⟶ Y}
    (φ : MapFactorizationData W₁ W₂ f) :
    MapFactorizationData W₂.unop W₁.unop f.unop where
  Z := φ.Z.unop
  i := φ.p.unop
  p := φ.i.unop
  hi := φ.hp
  hp := φ.hi
  fac := by simp [← unop_comp]

@[simps]
def opEquiv {W₁ W₂ : MorphismProperty C} {X Y : C} {f : X ⟶ Y} :
    MapFactorizationData W₁ W₂ f ≃ MapFactorizationData W₂.op W₁.op f.op where
  toFun φ := φ.op
  invFun φ := φ.unop

end CategoryTheory.MorphismProperty.MapFactorizationData
