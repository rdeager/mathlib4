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

/-- The pullback CommSq for the threefold pullback projection `(sq₃.p₁, sq₃.p₂)`.
Both paths `sq₃.p₁ ≫ f i₁` and `sq₃.p₂ ≫ f i₂` equal `sq₃.p`. -/
def pbCommSq₃ (i₁ i₂ i₃ : ι) :
    CommSq (f i₁).op.toLoc (f i₂).op.toLoc
      (sq₃ i₁ i₂ i₃).p₁.op.toLoc (sq₃ i₁ i₂ i₃).p₂.op.toLoc := by
  constructor
  change ((sq₃ i₁ i₂ i₃).p₁ ≫ f i₁).op.toLoc = ((sq₃ i₁ i₂ i₃).p₂ ≫ f i₂).op.toLoc
  rw [(sq₃ i₁ i₂ i₃).w₁, (sq₃ i₁ i₂ i₃).w₂]

/-- Similarly for `(sq₃.p₂, sq₃.p₃)`. -/
def pbCommSq₃' (i₁ i₂ i₃ : ι) :
    CommSq (f i₂).op.toLoc (f i₃).op.toLoc
      (sq₃ i₁ i₂ i₃).p₂.op.toLoc (sq₃ i₁ i₂ i₃).p₃.op.toLoc := by
  constructor
  change ((sq₃ i₁ i₂ i₃).p₂ ≫ f i₂).op.toLoc = ((sq₃ i₁ i₂ i₃).p₃ ≫ f i₃).op.toLoc
  rw [(sq₃ i₁ i₂ i₃).w₂, (sq₃ i₁ i₂ i₃).w₃]

/-- And for `(sq₃.p₁, sq₃.p₃)`. -/
def pbCommSq₃'' (i₁ i₂ i₃ : ι) :
    CommSq (f i₁).op.toLoc (f i₃).op.toLoc
      (sq₃ i₁ i₂ i₃).p₁.op.toLoc (sq₃ i₁ i₂ i₃).p₃.op.toLoc := by
  constructor
  change ((sq₃ i₁ i₂ i₃).p₁ ≫ f i₁).op.toLoc = ((sq₃ i₁ i₂ i₃).p₃ ≫ f i₃).op.toLoc
  rw [(sq₃ i₁ i₂ i₃).w₁, (sq₃ i₁ i₂ i₃).w₃]

set_option backward.isDefEq.respectTransparency false in
variable (F) in
/-- **Key helper**: pulling back `isoMapOfCommSq` along a morphism gives another
`isoMapOfCommSq` for the pulled-back square.

For the pullback square `(sq i₁ i₂)` with projections `p₁, p₂` and
the threefold pullback morphism `p₁₂ : P₁₂₃ → P₁₂`, the composition
```
mc'(sq.p₁, p₁₂, sq₃.p₁).hom ≫ p₁₂*(iso₁₂.hom.app(M)) ≫ mc'(sq.p₂, p₁₂, sq₃.p₂).inv
```
(which is `pullHom(iso₁₂.hom.app(M))(p₁₂)`) equals `isoMapOfCommSq(pbCommSq₃).hom.app(M)`.

The proof follows the same fusion pattern as `pullHom_pullHom'`. -/
lemma pullHom_isoMapOfCommSq (i₁ i₂ i₃ : ι)
    (M : (F.obj (.mk (Opposite.op S))).obj) :
    LocallyDiscreteOpToCat.pullHom
      (((F.comp Adj.forget₁).isoMapOfCommSq (pbCommSq sq i₁ i₂)).hom.toNatTrans.app M)
      (sq₃ i₁ i₂ i₃).p₁₂ (sq₃ i₁ i₂ i₃).p₁ (sq₃ i₁ i₂ i₃).p₂ =
    ((F.comp Adj.forget₁).isoMapOfCommSq (pbCommSq₃ sq sq₃ i₁ i₂ i₃)).hom.toNatTrans.app M := by
  -- Expand both sides via isoMapOfCommSq_eq
  rw [(F.comp Adj.forget₁).isoMapOfCommSq_eq (pbCommSq sq i₁ i₂)
    ((sq i₁ i₂).p₁ ≫ f i₁).op.toLoc (by rw [← Quiver.Hom.comp_toLoc, ← op_comp]),
    (F.comp Adj.forget₁).isoMapOfCommSq_eq (pbCommSq₃ sq sq₃ i₁ i₂ i₃)
    ((sq₃ i₁ i₂ i₃).p₁ ≫ f i₁).op.toLoc (by rw [← Quiver.Hom.comp_toLoc, ← op_comp])]
  simp only [Iso.trans_hom, Iso.symm_hom, Cat.Hom₂.comp_app]
  -- Unfold pullHom, distribute
  dsimp only [LocallyDiscreteOpToCat.pullHom]
  simp only [Functor.map_comp, Category.assoc]
  -- Use mapComp'₀₁₃_inv_app telescope for left pair:
  -- mc'(sq.p₁, p₁₂, sq₃.p₁).hom ≫ p₁₂*(mc'(fi₁, sq.p₁, c).inv) =
  --   mc'(fi₁, sq₃.p₁, c').inv ≫ mc'(c, p₁₂, c').hom
  -- (from: mc'(fi₁, sq₃.p₁, c').inv =
  --   mc'(sq.p₁, p₁₂, sq₃.p₁).hom ≫ p₁₂*(mc'(fi₁, sq.p₁, c).inv) ≫ mc'(c, p₁₂, c').inv)
  have exp₁ := (F.comp Adj.forget₁).mapComp'₀₁₃_inv_app
    (f i₁).op.toLoc (sq i₁ i₂).p₁.op.toLoc (sq₃ i₁ i₂ i₃).p₁₂.op.toLoc
    ((sq i₁ i₂).p₁ ≫ f i₁).op.toLoc (sq₃ i₁ i₂ i₃).p₁.op.toLoc
    ((sq₃ i₁ i₂ i₃).p₁ ≫ f i₁).op.toLoc
    (by rw [← Quiver.Hom.comp_toLoc, ← op_comp])
    (by rw [← Quiver.Hom.comp_toLoc, ← op_comp, (sq₃ i₁ i₂ i₃).p₁₂_p₁])
    (by rw [← Quiver.Hom.comp_toLoc, ← op_comp]) M
  -- Use mapComp'₀₂₃_hom_app for right pair (dual telescope):
  -- p₁₂*(mc'(fi₂, sq.p₂, c).hom) ≫ mc'(sq.p₂, p₁₂, sq₃.p₂).inv =
  --   mc'(c, p₁₂, c').inv ≫ mc'(fi₂, sq₃.p₂, c').hom
  have exp₂ := (F.comp Adj.forget₁).mapComp'₀₂₃_inv_app
    (f i₂).op.toLoc (sq i₁ i₂).p₂.op.toLoc (sq₃ i₁ i₂ i₃).p₁₂.op.toLoc
    ((sq i₁ i₂).p₁ ≫ f i₁).op.toLoc (sq₃ i₁ i₂ i₃).p₂.op.toLoc
    ((sq₃ i₁ i₂ i₃).p₁ ≫ f i₁).op.toLoc
    (by rw [← Quiver.Hom.comp_toLoc, ← op_comp, (sq i₁ i₂).condition.symm])
    (by rw [← Quiver.Hom.comp_toLoc, ← op_comp, (sq₃ i₁ i₂ i₃).p₁₂_p₂])
    (by simp [← Quiver.Hom.comp_toLoc, ← op_comp])
    M
  -- Now use exp₁ and exp₂ to transform the RHS into the LHS.
  -- exp₁: mc'(fi₁, sq₃.p₁, c').inv = [terms 1-2] ≫ mc'(c, p₁₂, c').inv
  -- exp₂: mc'(c, p₁₂, c').inv = [terms 3-4] ≫ mc'(fi₂, sq₃.p₂, c').inv
  -- So RHS = exp₁ ≫ mc'(fi₂, sq₃.p₂, c').hom
  --        = [terms 1-2] ≫ exp₂ ≫ mc'(fi₂, sq₃.p₂, c').hom
  --        = [terms 1-2] ≫ [terms 3-4] ≫ (mc'.inv ≫ mc'.hom = 𝟙) = LHS
  conv_rhs => rw [exp₁]
  simp only [Category.assoc]
  conv_rhs => rw [exp₂]
  simp only [Category.assoc]
  -- Cancel mc'(fi₂, sq₃.p₂, c').inv ≫ mc'(fi₂, sq₃.p₂, c').hom = 𝟙
  set_option backward.isDefEq.respectTransparency false in
  erw [Iso.inv_hom_id_app (Cat.Hom.toNatIso
    ((F.comp Adj.forget₁).mapComp' (f i₂).op.toLoc (sq₃ i₁ i₂ i₃).p₂.op.toLoc
      ((sq₃ i₁ i₂ i₃).p₁ ≫ f i₁).op.toLoc
      (by simp [← Quiver.Hom.comp_toLoc, ← op_comp])))]
  erw [Category.comp_id]

set_option backward.isDefEq.respectTransparency false in
variable (F) in
/-- Variant of `pullHom_isoMapOfCommSq` for the `(i₂, i₃)` square pulled back along `p₂₃`. -/
lemma pullHom_isoMapOfCommSq' (i₁ i₂ i₃ : ι)
    (M : (F.obj (.mk (Opposite.op S))).obj) :
    LocallyDiscreteOpToCat.pullHom
      (((F.comp Adj.forget₁).isoMapOfCommSq (pbCommSq sq i₂ i₃)).hom.toNatTrans.app M)
      (sq₃ i₁ i₂ i₃).p₂₃ (sq₃ i₁ i₂ i₃).p₂ (sq₃ i₁ i₂ i₃).p₃ =
    ((F.comp Adj.forget₁).isoMapOfCommSq (pbCommSq₃' sq sq₃ i₁ i₂ i₃)).hom.toNatTrans.app M := by
  rw [(F.comp Adj.forget₁).isoMapOfCommSq_eq (pbCommSq sq i₂ i₃)
    ((sq i₂ i₃).p₁ ≫ f i₂).op.toLoc (by rw [← Quiver.Hom.comp_toLoc, ← op_comp]),
    (F.comp Adj.forget₁).isoMapOfCommSq_eq (pbCommSq₃' sq sq₃ i₁ i₂ i₃)
    ((sq₃ i₁ i₂ i₃).p₂ ≫ f i₂).op.toLoc (by rw [← Quiver.Hom.comp_toLoc, ← op_comp])]
  simp only [Iso.trans_hom, Iso.symm_hom, Cat.Hom₂.comp_app]
  dsimp only [LocallyDiscreteOpToCat.pullHom]
  simp only [Functor.map_comp, Category.assoc]
  have exp₁ := (F.comp Adj.forget₁).mapComp'₀₁₃_inv_app
    (f i₂).op.toLoc (sq i₂ i₃).p₁.op.toLoc (sq₃ i₁ i₂ i₃).p₂₃.op.toLoc
    ((sq i₂ i₃).p₁ ≫ f i₂).op.toLoc (sq₃ i₁ i₂ i₃).p₂.op.toLoc
    ((sq₃ i₁ i₂ i₃).p₂ ≫ f i₂).op.toLoc
    (by rw [← Quiver.Hom.comp_toLoc, ← op_comp])
    (by rw [← Quiver.Hom.comp_toLoc, ← op_comp, (sq₃ i₁ i₂ i₃).p₂₃_p₂])
    (by rw [← Quiver.Hom.comp_toLoc, ← op_comp]) M
  have exp₂ := (F.comp Adj.forget₁).mapComp'₀₂₃_inv_app
    (f i₃).op.toLoc (sq i₂ i₃).p₂.op.toLoc (sq₃ i₁ i₂ i₃).p₂₃.op.toLoc
    ((sq i₂ i₃).p₁ ≫ f i₂).op.toLoc (sq₃ i₁ i₂ i₃).p₃.op.toLoc
    ((sq₃ i₁ i₂ i₃).p₂ ≫ f i₂).op.toLoc
    (by rw [← Quiver.Hom.comp_toLoc, ← op_comp, (sq i₂ i₃).condition.symm])
    (by rw [← Quiver.Hom.comp_toLoc, ← op_comp, (sq₃ i₁ i₂ i₃).p₂₃_p₃])
    (by simp [← Quiver.Hom.comp_toLoc, ← op_comp])
    M
  conv_rhs => rw [exp₁]
  simp only [Category.assoc]
  conv_rhs => rw [exp₂]
  simp only [Category.assoc]
  set_option backward.isDefEq.respectTransparency false in
  erw [Iso.inv_hom_id_app (Cat.Hom.toNatIso
    ((F.comp Adj.forget₁).mapComp' (f i₃).op.toLoc (sq₃ i₁ i₂ i₃).p₃.op.toLoc
      ((sq₃ i₁ i₂ i₃).p₂ ≫ f i₂).op.toLoc
      (by simp [← Quiver.Hom.comp_toLoc, ← op_comp])))]
  erw [Category.comp_id]

set_option backward.isDefEq.respectTransparency false in
variable (F) in
/-- Variant of `pullHom_isoMapOfCommSq` for the `(i₁, i₃)` square pulled back along `p₁₃`. -/
lemma pullHom_isoMapOfCommSq'' (i₁ i₂ i₃ : ι)
    (M : (F.obj (.mk (Opposite.op S))).obj) :
    LocallyDiscreteOpToCat.pullHom
      (((F.comp Adj.forget₁).isoMapOfCommSq (pbCommSq sq i₁ i₃)).hom.toNatTrans.app M)
      (sq₃ i₁ i₂ i₃).p₁₃ (sq₃ i₁ i₂ i₃).p₁ (sq₃ i₁ i₂ i₃).p₃ =
    ((F.comp Adj.forget₁).isoMapOfCommSq (pbCommSq₃'' sq sq₃ i₁ i₂ i₃)).hom.toNatTrans.app M := by
  rw [(F.comp Adj.forget₁).isoMapOfCommSq_eq (pbCommSq sq i₁ i₃)
    ((sq i₁ i₃).p₁ ≫ f i₁).op.toLoc (by rw [← Quiver.Hom.comp_toLoc, ← op_comp]),
    (F.comp Adj.forget₁).isoMapOfCommSq_eq (pbCommSq₃'' sq sq₃ i₁ i₂ i₃)
    ((sq₃ i₁ i₂ i₃).p₁ ≫ f i₁).op.toLoc (by rw [← Quiver.Hom.comp_toLoc, ← op_comp])]
  simp only [Iso.trans_hom, Iso.symm_hom, Cat.Hom₂.comp_app]
  dsimp only [LocallyDiscreteOpToCat.pullHom]
  simp only [Functor.map_comp, Category.assoc]
  have exp₁ := (F.comp Adj.forget₁).mapComp'₀₁₃_inv_app
    (f i₁).op.toLoc (sq i₁ i₃).p₁.op.toLoc (sq₃ i₁ i₂ i₃).p₁₃.op.toLoc
    ((sq i₁ i₃).p₁ ≫ f i₁).op.toLoc (sq₃ i₁ i₂ i₃).p₁.op.toLoc
    ((sq₃ i₁ i₂ i₃).p₁ ≫ f i₁).op.toLoc
    (by rw [← Quiver.Hom.comp_toLoc, ← op_comp])
    (by rw [← Quiver.Hom.comp_toLoc, ← op_comp, (sq₃ i₁ i₂ i₃).p₁₃_p₁])
    (by rw [← Quiver.Hom.comp_toLoc, ← op_comp]) M
  have exp₂ := (F.comp Adj.forget₁).mapComp'₀₂₃_inv_app
    (f i₃).op.toLoc (sq i₁ i₃).p₂.op.toLoc (sq₃ i₁ i₂ i₃).p₁₃.op.toLoc
    ((sq i₁ i₃).p₁ ≫ f i₁).op.toLoc (sq₃ i₁ i₂ i₃).p₃.op.toLoc
    ((sq₃ i₁ i₂ i₃).p₁ ≫ f i₁).op.toLoc
    (by rw [← Quiver.Hom.comp_toLoc, ← op_comp, (sq i₁ i₃).condition.symm])
    (by rw [← Quiver.Hom.comp_toLoc, ← op_comp, (sq₃ i₁ i₂ i₃).p₁₃_p₃])
    (by simp [← Quiver.Hom.comp_toLoc, ← op_comp])
    M
  conv_rhs => rw [exp₁]
  simp only [Category.assoc]
  conv_rhs => rw [exp₂]
  simp only [Category.assoc]
  set_option backward.isDefEq.respectTransparency false in
  erw [Iso.inv_hom_id_app (Cat.Hom.toNatIso
    ((F.comp Adj.forget₁).mapComp' (f i₃).op.toLoc (sq₃ i₁ i₂ i₃).p₃.op.toLoc
      ((sq₃ i₁ i₂ i₃).p₁ ≫ f i₁).op.toLoc
      (by simp [← Quiver.Hom.comp_toLoc, ← op_comp])))]
  erw [Category.comp_id]

set_option backward.isDefEq.respectTransparency false in
variable (F) in
/-- **Composition of threefold isoMapOfCommSq**: the coherence isos for `(i₁,i₂)` and
`(i₂,i₃)` pulled back to the threefold pullback compose to give the iso for `(i₁,i₃)`.

All three expand via `isoMapOfCommSq_eq` with common path `sq₃.p`, and the
middle `mapComp'(fi₂, sq₃.p₂).hom ≫ mapComp'(fi₂, sq₃.p₂).inv = 𝟙` cancels. -/
lemma isoMapOfCommSq₃_comp (i₁ i₂ i₃ : ι)
    (M : (F.obj (.mk (Opposite.op S))).obj) :
    ((F.comp Adj.forget₁).isoMapOfCommSq
      (pbCommSq₃ sq sq₃ i₁ i₂ i₃)).hom.toNatTrans.app M ≫
    ((F.comp Adj.forget₁).isoMapOfCommSq
      (pbCommSq₃' sq sq₃ i₁ i₂ i₃)).hom.toNatTrans.app M =
    ((F.comp Adj.forget₁).isoMapOfCommSq
      (pbCommSq₃'' sq sq₃ i₁ i₂ i₃)).hom.toNatTrans.app M := by
  -- Use the SAME common path φ = (sq₃.p₁ ≫ fi₁).op.toLoc for all three expansions.
  -- For pbCommSq₃' we need (sq₃.p₂ ≫ fi₂) = (sq₃.p₁ ≫ fi₁) (both = sq₃.p).
  have hw₁₂ : (sq₃ i₁ i₂ i₃).p₂ ≫ f i₂ = (sq₃ i₁ i₂ i₃).p₁ ≫ f i₁ :=
    (sq₃ i₁ i₂ i₃).w₂.trans (sq₃ i₁ i₂ i₃).w₁.symm
  rw [(F.comp Adj.forget₁).isoMapOfCommSq_eq (pbCommSq₃ sq sq₃ i₁ i₂ i₃)
    ((sq₃ i₁ i₂ i₃).p₁ ≫ f i₁).op.toLoc
    (by rw [← Quiver.Hom.comp_toLoc, ← op_comp]),
    (F.comp Adj.forget₁).isoMapOfCommSq_eq (pbCommSq₃' sq sq₃ i₁ i₂ i₃)
    ((sq₃ i₁ i₂ i₃).p₁ ≫ f i₁).op.toLoc
    (by rw [← Quiver.Hom.comp_toLoc, ← op_comp, hw₁₂]),
    (F.comp Adj.forget₁).isoMapOfCommSq_eq (pbCommSq₃'' sq sq₃ i₁ i₂ i₃)
    ((sq₃ i₁ i₂ i₃).p₁ ≫ f i₁).op.toLoc
    (by rw [← Quiver.Hom.comp_toLoc, ← op_comp])]
  simp only [Iso.trans_hom, Iso.symm_hom, Cat.Hom₂.comp_app, Category.assoc]
  -- Now the middle pair uses the SAME mapComp': hom ≫ inv = 𝟙
  -- Use slice_rhs or direct reassoc to cancel the middle pair
  conv_lhs =>
    rw [← Category.assoc
      (f := ((F.comp Adj.forget₁).mapComp' (f i₂).op.toLoc
        (sq₃ i₁ i₂ i₃).p₂.op.toLoc
        ((sq₃ i₁ i₂ i₃).p₁ ≫ f i₁).op.toLoc _).hom.toNatTrans.app M)]
  set_option backward.isDefEq.respectTransparency false in
  erw [Iso.hom_inv_id_app (Cat.Hom.toNatIso
    ((F.comp Adj.forget₁).mapComp' (f i₂).op.toLoc
      (sq₃ i₁ i₂ i₃).p₂.op.toLoc
      ((sq₃ i₁ i₂ i₃).p₁ ≫ f i₁).op.toLoc
      (by simp [← Quiver.Hom.comp_toLoc, ← op_comp, hw₁₂])))]
  erw [Category.id_comp]

set_option backward.isDefEq.respectTransparency false in
variable (F) in
/-- **Threefold cocycle at pullHom level** [Kahn, Proposition 3.3].
Pulling back `forwardHom(i₁,i₂)` and `forwardHom(i₂,i₃)` to the threefold pullback
via `pullHom` and composing gives `forwardHom(i₁,i₃)` pulled back.

The proof uses counit naturality, iso naturality, coalgebra coassociativity `D.coassoc`,
and the adjunction triangle identity `l(η) ≫ ε = 𝟙`. -/
lemma forwardHom_cocycle (D : F.DescentDataAsCoalgebra f) (i₁ i₂ i₃ : ι) :
    LocallyDiscreteOpToCat.pullHom (forwardHom F sq D i₁ i₂)
      (sq₃ i₁ i₂ i₃).p₁₂ (sq₃ i₁ i₂ i₃).p₁ (sq₃ i₁ i₂ i₃).p₂ ≫
    LocallyDiscreteOpToCat.pullHom (forwardHom F sq D i₂ i₃)
      (sq₃ i₁ i₂ i₃).p₂₃ (sq₃ i₁ i₂ i₃).p₂ (sq₃ i₁ i₂ i₃).p₃ =
    LocallyDiscreteOpToCat.pullHom (forwardHom F sq D i₁ i₃)
      (sq₃ i₁ i₂ i₃).p₁₃ (sq₃ i₁ i₂ i₃).p₁ (sq₃ i₁ i₂ i₃).p₃ := by
  -- Unfold pullHom and forwardHom, distribute
  dsimp only [LocallyDiscreteOpToCat.pullHom]
  simp only [Category.assoc]
  dsimp only [forwardHom]
  simp only [Functor.map_comp, Category.assoc]
  -- Push D.hom₁₂ out of block 1 past mc'₁
  set_option backward.isDefEq.respectTransparency false in
  conv_lhs =>
    rw [← Category.assoc, ← (F.comp Adj.forget₁).mapComp'_hom_naturality
      (sq i₁ i₂).p₁.op.toLoc (sq₃ i₁ i₂ i₃).p₁₂.op.toLoc (sq₃ i₁ i₂ i₃).p₁.op.toLoc
      (by rw [← Quiver.Hom.comp_toLoc, ← op_comp, (sq₃ i₁ i₂ i₃).p₁₂_p₁]) (D.hom i₁ i₂)]
  simp only [Category.assoc]
  -- Push all ε past mc'_inv
  set_option backward.isDefEq.respectTransparency false in
  simp only [mapComp'_inv_naturality]
  -- Push D.hom₂₃ past mc'₃ on LHS
  set_option backward.isDefEq.respectTransparency false in
  conv_lhs =>
    rw [← Category.assoc
      (f := ((F.comp Adj.forget₁).mapComp' (sq i₂ i₃).p₁.op.toLoc
        (sq₃ i₁ i₂ i₃).p₂₃.op.toLoc (sq₃ i₁ i₂ i₃).p₂.op.toLoc _).hom.toNatTrans.app _),
      ← (F.comp Adj.forget₁).mapComp'_hom_naturality
        (sq i₂ i₃).p₁.op.toLoc (sq₃ i₁ i₂ i₃).p₂₃.op.toLoc (sq₃ i₁ i₂ i₃).p₂.op.toLoc
        (by rw [← Quiver.Hom.comp_toLoc, ← op_comp, (sq₃ i₁ i₂ i₃).p₂₃_p₂]) (D.hom i₂ i₃)]
  simp only [Category.assoc]
  -- Push D.hom₁₃ past mc'₅ on RHS
  set_option backward.isDefEq.respectTransparency false in
  conv_rhs =>
    rw [← Category.assoc, ← (F.comp Adj.forget₁).mapComp'_hom_naturality
      (sq i₁ i₃).p₁.op.toLoc (sq₃ i₁ i₂ i₃).p₁₃.op.toLoc (sq₃ i₁ i₂ i₃).p₁.op.toLoc
      (by rw [← Quiver.Hom.comp_toLoc, ← op_comp, (sq₃ i₁ i₂ i₃).p₁₃_p₁]) (D.hom i₁ i₃)]
  simp only [Category.assoc]
  -- Push D.hom₂₃ back through mc'₂.inv on LHS (reverse naturality)
  set_option backward.isDefEq.respectTransparency false in
  rw [← (F.comp Adj.forget₁).mapComp'_inv_naturality_assoc
    (sq i₁ i₂).p₂.op.toLoc (sq₃ i₁ i₂ i₃).p₁₂.op.toLoc (sq₃ i₁ i₂ i₃).p₂.op.toLoc
    (by rw [← Quiver.Hom.comp_toLoc, ← op_comp, (sq₃ i₁ i₂ i₃).p₁₂_p₂]) (D.hom i₂ i₃)]
  -- Fold ε₂ ≫ D.hom₂₃ inside p₁₂*(sq.p₂*(...))
  conv_lhs =>
    rw [← Functor.map_comp_assoc
      (((F.comp Adj.forget₁).map (sq₃ i₁ i₂ i₃).p₁₂.op.toLoc).toFunctor)
      (((F.comp Adj.forget₁).map (sq i₁ i₂).p₂.op.toLoc).toFunctor.map
        ((F.map (f i₂).op.toLoc).adj.counit.toNatTrans.app (D.obj i₂)))
      (((F.comp Adj.forget₁).map (sq i₁ i₂).p₂.op.toLoc).toFunctor.map (D.hom i₂ i₃)),
      ← Functor.map_comp
        (((F.comp Adj.forget₁).map (sq i₁ i₂).p₂.op.toLoc).toFunctor)
        ((F.map (f i₂).op.toLoc).adj.counit.toNatTrans.app (D.obj i₂))
        (D.hom i₂ i₃)]
  -- Apply counit naturality: ε₂ ≫ D.hom₂₃ = l₂(r₂(D.hom₂₃)) ≫ ε₂
  rw [show (F.map (f i₂).op.toLoc).adj.counit.toNatTrans.app (D.obj i₂) ≫ D.hom i₂ i₃ =
    (F.map (f i₂).op.toLoc).l.toFunctor.map
      ((F.map (f i₂).op.toLoc).r.toFunctor.map (D.hom i₂ i₃)) ≫
    (F.map (f i₂).op.toLoc).adj.counit.toNatTrans.app _ from
    (Adj.counit_naturality (F.map (f i₂).op.toLoc) (D.hom i₂ i₃)).symm]
  -- Distribute l₂(r₂(D.hom₂₃)) ≫ ε₂ through sq.p₂* and p₁₂*
  simp only [Functor.map_comp, Category.assoc]
  -- Fold iso₁₂.app ≫ sq.p₂*(l₂(r₂(D.hom₂₃))) inside p₁₂* for iso naturality
  conv_lhs =>
    rw [← Functor.map_comp_assoc
      (((F.comp Adj.forget₁).map (sq₃ i₁ i₂ i₃).p₁₂.op.toLoc).toFunctor)
      (((F.comp Adj.forget₁).isoMapOfCommSq (pbCommSq sq i₁ i₂)).hom.toNatTrans.app
        ((F.map (f i₂).op.toLoc).r.toFunctor.obj (D.obj i₂)))
      (((F.comp Adj.forget₁).map (sq i₁ i₂).p₂.op.toLoc).toFunctor.map
        ((F.map (f i₂).op.toLoc).l.toFunctor.map
          ((F.map (f i₂).op.toLoc).r.toFunctor.map (D.hom i₂ i₃))))]
  -- Apply iso₁₂ naturality at r₂(D.hom₂₃)
  set_option backward.isDefEq.respectTransparency false in
  erw [← ((F.comp Adj.forget₁).isoMapOfCommSq (pbCommSq sq i₁ i₂)).hom.toNatTrans.naturality
    ((F.map (f i₂).op.toLoc).r.toFunctor.map (D.hom i₂ i₃))]
  -- Convert Cat composition form to explicit functor application
  erw [show ((F.comp Adj.forget₁).map (f i₁).op.toLoc ≫
    (F.comp Adj.forget₁).map (sq i₁ i₂).p₁.op.toLoc).toFunctor.map
      ((F.map (f i₂).op.toLoc).r.toFunctor.map (D.hom i₂ i₃)) =
    ((F.comp Adj.forget₁).map (sq i₁ i₂).p₁.op.toLoc).toFunctor.map
      (((F.comp Adj.forget₁).map (f i₁).op.toLoc).toFunctor.map
        ((F.map (f i₂).op.toLoc).r.toFunctor.map (D.hom i₂ i₃))) from rfl]
  simp only [Functor.map_comp, Category.assoc]
  -- Push l₁(r₂(D.hom₂₃)) from p₁₂*(sq.p₁*(...)) past mc'₁.hom to p₁ level
  have key₁ := (F.comp Adj.forget₁).mapComp'_hom_naturality
    (sq i₁ i₂).p₁.op.toLoc (sq₃ i₁ i₂ i₃).p₁₂.op.toLoc (sq₃ i₁ i₂ i₃).p₁.op.toLoc
    (by rw [← Quiver.Hom.comp_toLoc, ← op_comp, (sq₃ i₁ i₂ i₃).p₁₂_p₁])
    (a := ((F.comp Adj.forget₁).map (f i₁).op.toLoc).toFunctor.map
      ((F.map (f i₂).op.toLoc).r.toFunctor.map (D.hom i₂ i₃)))
  set_option backward.isDefEq.respectTransparency false in
  erw [show ((F.comp Adj.forget₁).mapComp' (sq i₁ i₂).p₁.op.toLoc
    (sq₃ i₁ i₂ i₃).p₁₂.op.toLoc (sq₃ i₁ i₂ i₃).p₁.op.toLoc _).hom.toNatTrans.app
    ((F.map (f i₁).op.toLoc).l.toFunctor.obj
      ((F.map (f i₂).op.toLoc).r.toFunctor.obj (D.obj i₂))) =
    ((F.comp Adj.forget₁).mapComp' (sq i₁ i₂).p₁.op.toLoc
      (sq₃ i₁ i₂ i₃).p₁₂.op.toLoc (sq₃ i₁ i₂ i₃).p₁.op.toLoc _).hom.toNatTrans.app
    (((F.comp Adj.forget₁).map (f i₁).op.toLoc).toFunctor.obj
      ((F.map (f i₂).op.toLoc).r.toFunctor.obj (D.obj i₂))) from rfl]
  set_option backward.isDefEq.respectTransparency false in
  rw [← Category.assoc (f := ((F.comp Adj.forget₁).mapComp' (sq i₁ i₂).p₁.op.toLoc
    (sq₃ i₁ i₂ i₃).p₁₂.op.toLoc (sq₃ i₁ i₂ i₃).p₁.op.toLoc _).hom.toNatTrans.app _),
    ← key₁]
  simp only [Category.assoc]
  -- Apply D.coassoc: D.hom₁₂ ≫ l₁(r₂(D.hom₂₃)) = D.hom₁₃ ≫ l₁(η₂)
  rw [← Functor.map_comp_assoc]
  set_option backward.isDefEq.respectTransparency false in
  erw [D.coassoc i₁ i₂ i₃]
  simp only [Functor.map_comp, Category.assoc]
  -- Strip common prefix p₁*(D.hom₁₃)
  congr 1
  -- Push l₁(η₂) past mc'₁.hom to p₁₂ level
  have key₂ := (F.comp Adj.forget₁).mapComp'_hom_naturality
    (sq i₁ i₂).p₁.op.toLoc (sq₃ i₁ i₂ i₃).p₁₂.op.toLoc (sq₃ i₁ i₂ i₃).p₁.op.toLoc
    (by rw [← Quiver.Hom.comp_toLoc, ← op_comp, (sq₃ i₁ i₂ i₃).p₁₂_p₁])
    (a := ((F.comp Adj.forget₁).map (f i₁).op.toLoc).toFunctor.map
      ((F.map (f i₂).op.toLoc).adj.unit.toNatTrans.app
        ((F.map (f i₃).op.toLoc).r.toFunctor.obj (D.obj i₃))))
  set_option backward.isDefEq.respectTransparency false in
  erw [show ((F.comp Adj.forget₁).map (sq₃ i₁ i₂ i₃).p₁.op.toLoc).toFunctor.map
    ((F.map (f i₁).op.toLoc).l.toFunctor.map
      ((F.map (f i₂).op.toLoc).adj.unit.toNatTrans.app
        ((F.map (f i₃).op.toLoc).r.toFunctor.1 (D.obj i₃)))) =
    ((F.comp Adj.forget₁).map (sq₃ i₁ i₂ i₃).p₁.op.toLoc).toFunctor.map
      (((F.comp Adj.forget₁).map (f i₁).op.toLoc).toFunctor.map
        ((F.map (f i₂).op.toLoc).adj.unit.toNatTrans.app
          ((F.map (f i₃).op.toLoc).r.toFunctor.obj (D.obj i₃)))) from rfl]
  set_option backward.isDefEq.respectTransparency false in
  erw [← Category.assoc
    (f := ((F.comp Adj.forget₁).map (sq₃ i₁ i₂ i₃).p₁.op.toLoc).toFunctor.map _),
    key₂]
  simp only [Category.assoc]
  -- TODO: remaining steps — iso naturality for η₂, triangle identity, iso block collapse
  sorry

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
  -- Rewrite pullHom' → pullHom via ChosenPullback₃, then apply the cocycle lemma
  rw [DescentData'.pullHom'₁₂_eq_pullHom_of_chosenPullback₃,
    DescentData'.pullHom'₂₃_eq_pullHom_of_chosenPullback₃,
    DescentData'.pullHom'₁₃_eq_pullHom_of_chosenPullback₃]
  exact forwardHom_cocycle F sq sq₃ D i₁ i₂ i₃

end ThreefoldCoherence

end Pseudofunctor

end CategoryTheory
