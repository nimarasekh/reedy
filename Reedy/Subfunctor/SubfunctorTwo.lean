/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.CategoryTheory.Subfunctor.Basic
public import Mathlib.CategoryTheory.Yoneda

/-!
# Subfunctors of bifuntors to types

-/

@[expose] public section

universe w v v' u u'

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  (F : C ⥤ D ⥤ Type w)

@[ext]
structure Subfunctor₂ where
  obj (U : C) (V : D) : Set ((F.obj U).obj V)
  map₁ {U₁ U₂ : C} (f : U₁ ⟶ U₂) (V : D) : obj U₁ V ⊆ ((F.map f).app V) ⁻¹' obj U₂ V
  map₂ (U : C) {V₁ V₂ : D} (g : V₁ ⟶ V₂) : obj U V₁ ⊆ ((F.obj U).map g) ⁻¹' obj U V₂

/-
* define a complete lattice structure similarly as in `CategoryTheory.Subfunctor.Basic`
* define a functor `Subfunctor₂ F ⥤ (C ⥤ D ⥤ Type w)` and show that it commutes
    with filtered colimits (this is similar to the result in the file
    `AlgebraicTopology.SimplicialSet.SubcomplexEvaluation`)
* more API which was developped only in the particular case `SSet.Subcomplex`
  (`AlgebraicTopology.SimplicialSet.Subcomplex`) should be generalized to `Subfunctor/Subfunctor₂`
-/

instance : CompleteLattice (Subfunctor₂ F) := sorry

namespace Subfunctor₂

variable {F}

@[simps]
def eval₁ (A : Subfunctor₂ F) (U : C) : Subfunctor (F.obj U) where
  obj V := A.obj U V
  map _ := A.map₂ _ _

@[simps]
def eval₂ (A : Subfunctor₂ F) (V : D) : Subfunctor (F.flip.obj V) where
  obj U := A.obj U V
  map _ := A.map₁ _ _

def toFunctor (A : Subfunctor₂ F) : C ⥤ D ⥤ Type w := sorry

def ι (A : Subfunctor₂ F) : A.toFunctor ⟶ F := sorry

variable (F) in
def toFunctorFunctor : Subfunctor₂ F ⥤ C ⥤ D ⥤ Type w where
  obj := toFunctor
  map := sorry

end Subfunctor₂

end CategoryTheory
