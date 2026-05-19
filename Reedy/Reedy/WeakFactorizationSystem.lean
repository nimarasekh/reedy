/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.MorphismProperty.WeakFactorizationSystem
public import Reedy.Arrow.ObjectProperty
public import Reedy.Reedy.Skeleton

/-!
# Skeleton

-/

universe u

@[expose] public section

namespace CategoryTheory

open HomotopicalAlgebra Limits

variable {C : Type u} [SmallCategory C] {W₁ W₂ : MorphismProperty C}
  [W₁.IsMultiplicative] [W₂.IsMultiplicative]
  {α : Type*} [LinearOrder α] [OrderBot α] [SuccOrder α] [WellFoundedLT α]

namespace ReedyStructure

open MorphismProperty

variable (r : ReedyStructure W₁ W₂ α) {D : Type*} [Category D]
  [HasColimitsOfSize.{u, u} D]
  (P₁ : MorphismProperty D) (P₂ : MorphismProperty D)

def left : MorphismProperty (C ⥤ D) :=
  ⨅ (X : C), .ofArrowObj (P₁.arrowObj.inverseImage (r.relativeLatchingFunctor X))

def right : MorphismProperty (C ⥤ D) :=
  ⨅ (X : C), .ofArrowObj (P₂.arrowObj.inverseImage (r.relativeMatchingFunctor X))

instance [P₁.IsStableUnderRetracts] : (r.left P₁).IsStableUnderRetracts := sorry

instance [P₂.IsStableUnderRetracts] : (r.right P₂).IsStableUnderRetracts := sorry

instance : (r.right P₂).IsStableUnderRetracts := sorry

-- C.5.5
instance isWeakFactorizationSystem [IsWeakFactorizationSystem P₁ P₂] :
    IsWeakFactorizationSystem (r.left P₁) (r.right P₂) := by
  have : P₁.IsStableUnderRetracts := by rw [← llp_eq_of_wfs P₁ P₂]; infer_instance
  have : P₂.IsStableUnderRetracts := by rw [← rlp_eq_of_wfs P₁ P₂]; infer_instance
  apply +allowSynthFailures IsWeakFactorizationSystem.mk'
  · -- C.5.7
    sorry
  · -- C.5.6
    sorry

end ReedyStructure

end CategoryTheory
