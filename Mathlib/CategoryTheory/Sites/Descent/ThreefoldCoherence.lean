/-
Copyright (c) 2026 Richard Eager. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Richard Eager
-/
module

public import Mathlib.CategoryTheory.Sites.Descent.DiagonalCoherence

/-!
# Threefold coherence for forward cocycle

Given a pseudofunctor `F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Adj Cat` and coalgebra-style
descent data `D : F.DescentDataAsCoalgebra f`, the forward-constructed descent datum
`ξ(D.hom i₁ i₂) = p₁^*(D.hom) ≫ isoMapOfCommSq ≫ p₂^*(ε)` satisfies the cocycle
condition on the threefold pullback.

This is [Kahn, Proposition 3.3]: the coalgebra coassociativity implies the cocycle
condition for the forward-constructed descent data.

## Main results

* `forwardHom`: the forward compatibility morphism over a chosen pullback
* `pullHom'_forwardHom_comp`: the cocycle condition for `forwardHom` on
  the threefold pullback

## References

* [B. Kahn, *Descente galoisienne et isogénies*, arXiv:2404.00868][kahn-2024]
-/

@[expose] public section

universe t v' v u' u

namespace CategoryTheory

open Bicategory Opposite Limits

namespace Pseudofunctor

variable {C : Type u} [Category.{v} C]
  {F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Adj Cat.{v', u'}}

section ThreefoldCoherence

variable {ι : Type t} {S : C} {X : ι → C} {f : ∀ i, X i ⟶ S}
  (sq : ∀ i j, ChosenPullback (f i) (f j))
  (sq₃ : ∀ (i₁ i₂ i₃ : ι), ChosenPullback₃ (sq i₁ i₂) (sq i₂ i₃) (sq i₁ i₃))

set_option backward.isDefEq.respectTransparency false in
variable (F) in
/-- [Kahn Eq (1.3)] The forward compatibility morphism over the chosen pullback at `(i₁, i₂)`.
This is `ξ(D.hom i₁ i₂) = p₁^*(D.hom) ≫ isoMapOfCommSq ≫ p₂^*(ε)`.

This is the same morphism used in `toDescentData'Obj.hom`, extracted as a standalone
definition so that coherence lemmas can be stated about it. -/
noncomputable def forwardHom (D : F.DescentDataAsCoalgebra f) (i₁ i₂ : ι) :
    ((F.comp Adj.forget₁).map (sq i₁ i₂).p₁.op.toLoc).toFunctor.obj (D.obj i₁) ⟶
    ((F.comp Adj.forget₁).map (sq i₁ i₂).p₂.op.toLoc).toFunctor.obj (D.obj i₂) :=
  -- Step 1: Apply p₁^* to coalgebra structure map
  ((F.comp Adj.forget₁).map (sq i₁ i₂).p₁.op.toLoc).toFunctor.map (D.hom i₁ i₂) ≫
  -- Step 2: isoMapOfCommSq for the pullback square
  ((F.comp Adj.forget₁).isoMapOfCommSq (pbCommSq sq i₁ i₂)).hom.toNatTrans.app
    ((F.map (f i₂).op.toLoc).r.toFunctor.obj (D.obj i₂)) ≫
  -- Step 3: p₂^* applied to counit
  ((F.comp Adj.forget₁).map (sq i₁ i₂).p₂.op.toLoc).toFunctor.map
    ((F.map (f i₂).op.toLoc).adj.counit.toNatTrans.app (D.obj i₂))

set_option backward.isDefEq.respectTransparency false in
variable (F) in
/-- **Threefold cocycle** [Kahn, Proposition 3.3]. The forward-constructed descent datum
satisfies the cocycle condition: pulling back `ξ₁₂` and `ξ₂₃` to the threefold pullback
and composing gives `ξ₁₃`.

The proof uses the coalgebra coassociativity `D.coassoc` and the adjunction triangle
identity `l(η) ≫ ε = 𝟙`. -/
lemma pullHom'_forwardHom_comp (D : F.DescentDataAsCoalgebra f) (i₁ i₂ i₃ : ι) :
    DescentData'.pullHom' (forwardHom F sq D) (sq₃ i₁ i₂ i₃).p
      (sq₃ i₁ i₂ i₃).p₁ (sq₃ i₁ i₂ i₃).p₂ ≫
    DescentData'.pullHom' (forwardHom F sq D) (sq₃ i₁ i₂ i₃).p
      (sq₃ i₁ i₂ i₃).p₂ (sq₃ i₁ i₂ i₃).p₃ =
    DescentData'.pullHom' (forwardHom F sq D) (sq₃ i₁ i₂ i₃).p
      (sq₃ i₁ i₂ i₃).p₁ (sq₃ i₁ i₂ i₃).p₃ := by
  -- Step 1: Rewrite pullHom' → pullHom via ChosenPullback₃
  rw [DescentData'.pullHom'₁₂_eq_pullHom_of_chosenPullback₃,
    DescentData'.pullHom'₂₃_eq_pullHom_of_chosenPullback₃,
    DescentData'.pullHom'₁₃_eq_pullHom_of_chosenPullback₃]
  -- Step 2: Unfold pullHom and forwardHom
  dsimp only [LocallyDiscreteOpToCat.pullHom, forwardHom]
  -- Step 3: Distribute functor maps and reassociate
  simp only [Functor.map_comp, Category.assoc]
  -- Step 4: Push D.hom i₁ i₂ past mc'₁ on LHS
  set_option backward.isDefEq.respectTransparency false in
  conv_lhs =>
    rw [← Category.assoc, ← (F.comp Adj.forget₁).mapComp'_hom_naturality
      (sq i₁ i₂).p₁.op.toLoc (sq₃ i₁ i₂ i₃).p₁₂.op.toLoc (sq₃ i₁ i₂ i₃).p₁.op.toLoc
      (by rw [← Quiver.Hom.comp_toLoc, ← op_comp, (sq₃ i₁ i₂ i₃).p₁₂_p₁]) (D.hom i₁ i₂)]
  simp only [Category.assoc]
  -- Step 5: Push D.hom i₂ i₃ past mc'₃ on LHS
  set_option backward.isDefEq.respectTransparency false in
  conv_lhs =>
    rw [← Category.assoc
      (f := ((F.comp Adj.forget₁).mapComp' (sq i₂ i₃).p₁.op.toLoc
        (sq₃ i₁ i₂ i₃).p₂₃.op.toLoc (sq₃ i₁ i₂ i₃).p₂.op.toLoc _).hom.toNatTrans.app _),
      ← (F.comp Adj.forget₁).mapComp'_hom_naturality
        (sq i₂ i₃).p₁.op.toLoc (sq₃ i₁ i₂ i₃).p₂₃.op.toLoc (sq₃ i₁ i₂ i₃).p₂.op.toLoc
        (by rw [← Quiver.Hom.comp_toLoc, ← op_comp, (sq₃ i₁ i₂ i₃).p₂₃_p₂]) (D.hom i₂ i₃)]
  simp only [Category.assoc]
  -- Step 6: Push D.hom i₁ i₃ past mc'₅ on RHS
  set_option backward.isDefEq.respectTransparency false in
  conv_rhs =>
    rw [← Category.assoc, ← (F.comp Adj.forget₁).mapComp'_hom_naturality
      (sq i₁ i₃).p₁.op.toLoc (sq₃ i₁ i₂ i₃).p₁₃.op.toLoc (sq₃ i₁ i₂ i₃).p₁.op.toLoc
      (by rw [← Quiver.Hom.comp_toLoc, ← op_comp, (sq₃ i₁ i₂ i₃).p₁₃_p₁]) (D.hom i₁ i₃)]
  simp only [Category.assoc]
  -- Step 7: Push all ε past mc'_inv on both sides
  set_option backward.isDefEq.respectTransparency false in
  simp only [mapComp'_inv_naturality]
  sorry

end ThreefoldCoherence

end Pseudofunctor

end CategoryTheory
