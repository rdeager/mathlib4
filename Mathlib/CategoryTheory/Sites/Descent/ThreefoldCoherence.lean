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

open Bicategory Opposite Limits LocallyDiscreteOpToCat

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
/-- Pulling back `isoMapOfCommSq` along a morphism that factors through the pullback
gives the `isoMapOfCommSq` for the pulled-back CommSq.

Given a `ChosenPullback (f j₁) (f j₂)` with projections `p₁, p₂` and a morphism
`p : T ⟶ pullback` with `p ≫ p₁ = q₁` and `p ≫ p₂ = q₂`, the `pullHom` of
`isoMapOfCommSq(pbCommSq)` along `p` equals `isoMapOfCommSq` for the CommSq
formed by `(q₁, q₂)`.

The three specific lemmas `pullHom_isoMapOfCommSq{,'',''}` are instances of this
for the threefold pullback projections `p₁₂, p₂₃, p₁₃`. -/
lemma pullHom_isoMapOfCommSq_of_factorization
    {j₁ j₂ : ι} {T : C}
    (p : T ⟶ (sq j₁ j₂).pullback) (q₁ : T ⟶ X j₁) (q₂ : T ⟶ X j₂)
    (hp₁ : p ≫ (sq j₁ j₂).p₁ = q₁) (hp₂ : p ≫ (sq j₁ j₂).p₂ = q₂)
    (csq : CommSq (f j₁).op.toLoc (f j₂).op.toLoc q₁.op.toLoc q₂.op.toLoc)
    (M : (F.obj (.mk (Opposite.op S))).obj) :
    LocallyDiscreteOpToCat.pullHom
      (((F.comp Adj.forget₁).isoMapOfCommSq (pbCommSq sq j₁ j₂)).hom.toNatTrans.app M)
      p q₁ q₂ =
    ((F.comp Adj.forget₁).isoMapOfCommSq csq).hom.toNatTrans.app M := by
  have hw : q₁ ≫ f j₁ = q₂ ≫ f j₂ := by
    rw [← hp₁, ← hp₂, Category.assoc, Category.assoc, (sq j₁ j₂).condition]
  rw [(F.comp Adj.forget₁).isoMapOfCommSq_eq (pbCommSq sq j₁ j₂)
    ((sq j₁ j₂).p₁ ≫ f j₁).op.toLoc (comp_op_toLoc _ _),
    (F.comp Adj.forget₁).isoMapOfCommSq_eq csq
    (q₁ ≫ f j₁).op.toLoc (comp_op_toLoc _ _)]
  simp only [Iso.trans_hom, Iso.symm_hom, Cat.Hom₂.comp_app]
  dsimp only [LocallyDiscreteOpToCat.pullHom]
  simp only [Functor.map_comp, Category.assoc]
  have exp₁ := (F.comp Adj.forget₁).mapComp'₀₁₃_inv_app
    (f j₁).op.toLoc (sq j₁ j₂).p₁.op.toLoc p.op.toLoc
    ((sq j₁ j₂).p₁ ≫ f j₁).op.toLoc q₁.op.toLoc
    (q₁ ≫ f j₁).op.toLoc
    (comp_op_toLoc _ _)
    (by rw [comp_op_toLoc, hp₁])
    (comp_op_toLoc _ _) M
  have exp₂ := (F.comp Adj.forget₁).mapComp'₀₂₃_inv_app
    (f j₂).op.toLoc (sq j₁ j₂).p₂.op.toLoc p.op.toLoc
    ((sq j₁ j₂).p₁ ≫ f j₁).op.toLoc q₂.op.toLoc
    (q₁ ≫ f j₁).op.toLoc
    (by rw [comp_op_toLoc, (sq j₁ j₂).condition.symm])
    (by rw [comp_op_toLoc, hp₂])
    (by rw [← Quiver.Hom.comp_toLoc, ← op_comp, ← Category.assoc, hp₁])
    M
  conv_rhs => rw [exp₁]
  simp only [Category.assoc]
  conv_rhs => rw [exp₂]
  simp only [Category.assoc]
  simp only [Cat.Hom.inv_hom_id_toNatTrans_app]
  erw [Category.comp_id]

variable (F) in
/-- Instance of `pullHom_isoMapOfCommSq_of_factorization` for `(i₁, i₂)` via `p₁₂`. -/
lemma pullHom_isoMapOfCommSq (i₁ i₂ i₃ : ι)
    (M : (F.obj (.mk (Opposite.op S))).obj) :
    LocallyDiscreteOpToCat.pullHom
      (((F.comp Adj.forget₁).isoMapOfCommSq (pbCommSq sq i₁ i₂)).hom.toNatTrans.app M)
      (sq₃ i₁ i₂ i₃).p₁₂ (sq₃ i₁ i₂ i₃).p₁ (sq₃ i₁ i₂ i₃).p₂ =
    ((F.comp Adj.forget₁).isoMapOfCommSq (pbCommSq₃ sq sq₃ i₁ i₂ i₃)).hom.toNatTrans.app M :=
  pullHom_isoMapOfCommSq_of_factorization F sq
    (sq₃ i₁ i₂ i₃).p₁₂ (sq₃ i₁ i₂ i₃).p₁ (sq₃ i₁ i₂ i₃).p₂
    (sq₃ i₁ i₂ i₃).p₁₂_p₁ (sq₃ i₁ i₂ i₃).p₁₂_p₂ (pbCommSq₃ sq sq₃ i₁ i₂ i₃) M

variable (F) in
/-- Instance of `pullHom_isoMapOfCommSq_of_factorization` for `(i₂, i₃)` via `p₂₃`. -/
lemma pullHom_isoMapOfCommSq' (i₁ i₂ i₃ : ι)
    (M : (F.obj (.mk (Opposite.op S))).obj) :
    LocallyDiscreteOpToCat.pullHom
      (((F.comp Adj.forget₁).isoMapOfCommSq (pbCommSq sq i₂ i₃)).hom.toNatTrans.app M)
      (sq₃ i₁ i₂ i₃).p₂₃ (sq₃ i₁ i₂ i₃).p₂ (sq₃ i₁ i₂ i₃).p₃ =
    ((F.comp Adj.forget₁).isoMapOfCommSq (pbCommSq₃' sq sq₃ i₁ i₂ i₃)).hom.toNatTrans.app M :=
  pullHom_isoMapOfCommSq_of_factorization F sq
    (sq₃ i₁ i₂ i₃).p₂₃ (sq₃ i₁ i₂ i₃).p₂ (sq₃ i₁ i₂ i₃).p₃
    (sq₃ i₁ i₂ i₃).p₂₃_p₂ (sq₃ i₁ i₂ i₃).p₂₃_p₃ (pbCommSq₃' sq sq₃ i₁ i₂ i₃) M

variable (F) in
/-- Instance of `pullHom_isoMapOfCommSq_of_factorization` for `(i₁, i₃)` via `p₁₃`. -/
lemma pullHom_isoMapOfCommSq'' (i₁ i₂ i₃ : ι)
    (M : (F.obj (.mk (Opposite.op S))).obj) :
    LocallyDiscreteOpToCat.pullHom
      (((F.comp Adj.forget₁).isoMapOfCommSq (pbCommSq sq i₁ i₃)).hom.toNatTrans.app M)
      (sq₃ i₁ i₂ i₃).p₁₃ (sq₃ i₁ i₂ i₃).p₁ (sq₃ i₁ i₂ i₃).p₃ =
    ((F.comp Adj.forget₁).isoMapOfCommSq (pbCommSq₃'' sq sq₃ i₁ i₂ i₃)).hom.toNatTrans.app M :=
  pullHom_isoMapOfCommSq_of_factorization F sq
    (sq₃ i₁ i₂ i₃).p₁₃ (sq₃ i₁ i₂ i₃).p₁ (sq₃ i₁ i₂ i₃).p₃
    (sq₃ i₁ i₂ i₃).p₁₃_p₁ (sq₃ i₁ i₂ i₃).p₁₃_p₃ (pbCommSq₃'' sq sq₃ i₁ i₂ i₃) M

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
    (comp_op_toLoc _ _),
    (F.comp Adj.forget₁).isoMapOfCommSq_eq (pbCommSq₃' sq sq₃ i₁ i₂ i₃)
    ((sq₃ i₁ i₂ i₃).p₁ ≫ f i₁).op.toLoc
    (by rw [comp_op_toLoc, hw₁₂]),
    (F.comp Adj.forget₁).isoMapOfCommSq_eq (pbCommSq₃'' sq sq₃ i₁ i₂ i₃)
    ((sq₃ i₁ i₂ i₃).p₁ ≫ f i₁).op.toLoc
    (comp_op_toLoc _ _)]
  simp only [Iso.trans_hom, Iso.symm_hom, Cat.Hom₂.comp_app, Category.assoc]
  -- Now the middle pair uses the SAME mapComp': hom ≫ inv = 𝟙
  -- Use slice_rhs or direct reassoc to cancel the middle pair
  conv_lhs =>
    rw [← Category.assoc
      (f := ((F.comp Adj.forget₁).mapComp' (f i₂).op.toLoc
        (sq₃ i₁ i₂ i₃).p₂.op.toLoc
        ((sq₃ i₁ i₂ i₃).p₁ ≫ f i₁).op.toLoc _).hom.toNatTrans.app M)]
  simp only [Cat.Hom.hom_inv_id_toNatTrans_app]
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
  conv_lhs =>
    rw [← Category.assoc, ← (F.comp Adj.forget₁).mapComp'_hom_naturality
      (sq i₁ i₂).p₁.op.toLoc (sq₃ i₁ i₂ i₃).p₁₂.op.toLoc (sq₃ i₁ i₂ i₃).p₁.op.toLoc
      (by rw [comp_op_toLoc, (sq₃ i₁ i₂ i₃).p₁₂_p₁]) (D.hom i₁ i₂)]
  simp only [Category.assoc]
  -- Push all ε past mc'_inv
  simp only [mapComp'_inv_naturality]
  -- Push D.hom₂₃ past mc'₃ on LHS
  conv_lhs =>
    rw [← Category.assoc
      (f := ((F.comp Adj.forget₁).mapComp' (sq i₂ i₃).p₁.op.toLoc
        (sq₃ i₁ i₂ i₃).p₂₃.op.toLoc (sq₃ i₁ i₂ i₃).p₂.op.toLoc _).hom.toNatTrans.app _),
      ← (F.comp Adj.forget₁).mapComp'_hom_naturality
        (sq i₂ i₃).p₁.op.toLoc (sq₃ i₁ i₂ i₃).p₂₃.op.toLoc (sq₃ i₁ i₂ i₃).p₂.op.toLoc
        (by rw [comp_op_toLoc, (sq₃ i₁ i₂ i₃).p₂₃_p₂]) (D.hom i₂ i₃)]
  simp only [Category.assoc]
  -- Push D.hom₁₃ past mc'₅ on RHS
  conv_rhs =>
    rw [← Category.assoc, ← (F.comp Adj.forget₁).mapComp'_hom_naturality
      (sq i₁ i₃).p₁.op.toLoc (sq₃ i₁ i₂ i₃).p₁₃.op.toLoc (sq₃ i₁ i₂ i₃).p₁.op.toLoc
      (by rw [comp_op_toLoc, (sq₃ i₁ i₂ i₃).p₁₃_p₁]) (D.hom i₁ i₃)]
  simp only [Category.assoc]
  -- Push D.hom₂₃ back through mc'₂.inv on LHS (reverse naturality)
  rw [← (F.comp Adj.forget₁).mapComp'_inv_naturality_assoc
    (sq i₁ i₂).p₂.op.toLoc (sq₃ i₁ i₂ i₃).p₁₂.op.toLoc (sq₃ i₁ i₂ i₃).p₂.op.toLoc
    (by rw [comp_op_toLoc, (sq₃ i₁ i₂ i₃).p₁₂_p₂]) (D.hom i₂ i₃)]
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
  erw [← ((F.comp Adj.forget₁).isoMapOfCommSq (pbCommSq sq i₁ i₂)).hom.toNatTrans.naturality
    ((F.map (f i₂).op.toLoc).r.toFunctor.map (D.hom i₂ i₃))]
  -- Convert Cat composition form to explicit functor application
  simp only [Cat.Hom.comp_toFunctor_map, Functor.map_comp, Category.assoc]
  -- Push l₁(r₂(D.hom₂₃)) from p₁₂*(sq.p₁*(...)) past mc'₁.hom to p₁ level
  have key₁ := (F.comp Adj.forget₁).mapComp'_hom_naturality
    (sq i₁ i₂).p₁.op.toLoc (sq₃ i₁ i₂ i₃).p₁₂.op.toLoc (sq₃ i₁ i₂ i₃).p₁.op.toLoc
    (by rw [comp_op_toLoc, (sq₃ i₁ i₂ i₃).p₁₂_p₁])
    (a := ((F.comp Adj.forget₁).map (f i₁).op.toLoc).toFunctor.map
      ((F.map (f i₂).op.toLoc).r.toFunctor.map (D.hom i₂ i₃)))
  erw [show ((F.comp Adj.forget₁).mapComp' (sq i₁ i₂).p₁.op.toLoc
    (sq₃ i₁ i₂ i₃).p₁₂.op.toLoc (sq₃ i₁ i₂ i₃).p₁.op.toLoc _).hom.toNatTrans.app
    ((F.map (f i₁).op.toLoc).l.toFunctor.obj
      ((F.map (f i₂).op.toLoc).r.toFunctor.obj (D.obj i₂))) =
    ((F.comp Adj.forget₁).mapComp' (sq i₁ i₂).p₁.op.toLoc
      (sq₃ i₁ i₂ i₃).p₁₂.op.toLoc (sq₃ i₁ i₂ i₃).p₁.op.toLoc _).hom.toNatTrans.app
    (((F.comp Adj.forget₁).map (f i₁).op.toLoc).toFunctor.obj
      ((F.map (f i₂).op.toLoc).r.toFunctor.obj (D.obj i₂))) from rfl]
  rw [← Category.assoc (f := ((F.comp Adj.forget₁).mapComp' (sq i₁ i₂).p₁.op.toLoc
    (sq₃ i₁ i₂ i₃).p₁₂.op.toLoc (sq₃ i₁ i₂ i₃).p₁.op.toLoc _).hom.toNatTrans.app _),
    ← key₁]
  simp only [Category.assoc]
  -- Apply D.coassoc: D.hom₁₂ ≫ l₁(r₂(D.hom₂₃)) = D.hom₁₃ ≫ l₁(η₂)
  rw [← Functor.map_comp_assoc]
  erw [D.coassoc i₁ i₂ i₃]
  simp only [Functor.map_comp, Category.assoc]
  -- Strip common prefix p₁*(D.hom₁₃)
  congr 1
  -- Push l₁(η₂) past mc'₁.hom to p₁₂ level
  have key₂ := (F.comp Adj.forget₁).mapComp'_hom_naturality
    (sq i₁ i₂).p₁.op.toLoc (sq₃ i₁ i₂ i₃).p₁₂.op.toLoc (sq₃ i₁ i₂ i₃).p₁.op.toLoc
    (by rw [comp_op_toLoc, (sq₃ i₁ i₂ i₃).p₁₂_p₁])
    (a := ((F.comp Adj.forget₁).map (f i₁).op.toLoc).toFunctor.map
      ((F.map (f i₂).op.toLoc).adj.unit.toNatTrans.app
        ((F.map (f i₃).op.toLoc).r.toFunctor.obj (D.obj i₃))))
  erw [show ((F.comp Adj.forget₁).map (sq₃ i₁ i₂ i₃).p₁.op.toLoc).toFunctor.map
    ((F.map (f i₁).op.toLoc).l.toFunctor.map
      ((F.map (f i₂).op.toLoc).adj.unit.toNatTrans.app
        ((F.map (f i₃).op.toLoc).r.toFunctor.1 (D.obj i₃)))) =
    ((F.comp Adj.forget₁).map (sq₃ i₁ i₂ i₃).p₁.op.toLoc).toFunctor.map
      (((F.comp Adj.forget₁).map (f i₁).op.toLoc).toFunctor.map
        ((F.map (f i₂).op.toLoc).adj.unit.toNatTrans.app
          ((F.map (f i₃).op.toLoc).r.toFunctor.obj (D.obj i₃)))) from rfl]
  erw [← Category.assoc
    (f := ((F.comp Adj.forget₁).map (sq₃ i₁ i₂ i₃).p₁.op.toLoc).toFunctor.map _),
    key₂]
  simp only [Category.assoc]
  -- Step 18: Fold p₁₂*(sq.p₁*(l₁(η₂))) ≫ p₁₂*(iso₁₂.app) inside p₁₂*
  conv_lhs =>
    rw [← Functor.map_comp_assoc
      (((F.comp Adj.forget₁).map (sq₃ i₁ i₂ i₃).p₁₂.op.toLoc).toFunctor)
      (((F.comp Adj.forget₁).map (sq i₁ i₂).p₁.op.toLoc).toFunctor.map
        (((F.comp Adj.forget₁).map (f i₁).op.toLoc).toFunctor.map
          ((F.map (f i₂).op.toLoc).adj.unit.toNatTrans.app
            ((F.map (f i₃).op.toLoc).r.toFunctor.obj (D.obj i₃)))))
      (((F.comp Adj.forget₁).isoMapOfCommSq (pbCommSq sq i₁ i₂)).hom.toNatTrans.app
        ((F.map (f i₂).op.toLoc).r.toFunctor.obj
          ((F.map (f i₂).op.toLoc).l.toFunctor.obj
            ((F.map (f i₃).op.toLoc).r.toFunctor.obj (D.obj i₃)))))]
  -- Step 19: Apply iso₁₂ naturality at η₂ (forward direction)
  erw [((F.comp Adj.forget₁).isoMapOfCommSq
    (pbCommSq sq i₁ i₂)).hom.toNatTrans.naturality
    ((F.map (f i₂).op.toLoc).adj.unit.toNatTrans.app
      ((F.map (f i₃).op.toLoc).r.toFunctor.obj (D.obj i₃)))]
  -- Convert Cat composition form
  simp only [Cat.Hom.comp_toFunctor_map, Functor.map_comp, Category.assoc]
  -- Step 20: Fold l₂(η₂) ≫ ε₂ inside sq.p₂* and apply triangle identity
  conv_lhs =>
    rw [← Functor.map_comp_assoc
      (((F.comp Adj.forget₁).map (sq₃ i₁ i₂ i₃).p₁₂.op.toLoc).toFunctor)
      (((F.comp Adj.forget₁).map (sq i₁ i₂).p₂.op.toLoc).toFunctor.map
        (((F.comp Adj.forget₁).map (f i₂).op.toLoc).toFunctor.map
          ((F.map (f i₂).op.toLoc).adj.unit.toNatTrans.app
            ((F.map (f i₃).op.toLoc).r.toFunctor.obj (D.obj i₃)))))
      (((F.comp Adj.forget₁).map (sq i₁ i₂).p₂.op.toLoc).toFunctor.map
        ((F.map (f i₂).op.toLoc).adj.counit.toNatTrans.app
          ((F.map (f i₂).op.toLoc).l.toFunctor.obj
            ((F.map (f i₃).op.toLoc).r.toFunctor.obj (D.obj i₃))))),
      ← Functor.map_comp
        (((F.comp Adj.forget₁).map (sq i₁ i₂).p₂.op.toLoc).toFunctor)]
  erw [Adj.left_triangle_components (F.map (f i₂).op.toLoc)]
  erw [Functor.map_id, Functor.map_id]
  simp only [Category.id_comp]
  -- Step 21: Goal has two iso blocks (LHS) vs one (RHS), both ≫ p₃*(ε₃).
  -- State the goal in folded pullHom form, prove it, then convert via dsimp.
  suffices h :
      LocallyDiscreteOpToCat.pullHom
        (((F.comp Adj.forget₁).isoMapOfCommSq
          (pbCommSq sq i₁ i₂)).hom.toNatTrans.app
          ((F.map (f i₃).op.toLoc).r.toFunctor.obj (D.obj i₃)))
        (sq₃ i₁ i₂ i₃).p₁₂ (sq₃ i₁ i₂ i₃).p₁ (sq₃ i₁ i₂ i₃).p₂ ≫
      LocallyDiscreteOpToCat.pullHom
        (((F.comp Adj.forget₁).isoMapOfCommSq
          (pbCommSq sq i₂ i₃)).hom.toNatTrans.app
          ((F.map (f i₃).op.toLoc).r.toFunctor.obj (D.obj i₃)))
        (sq₃ i₁ i₂ i₃).p₂₃ (sq₃ i₁ i₂ i₃).p₂ (sq₃ i₁ i₂ i₃).p₃ ≫
      ((F.comp Adj.forget₁).map (sq₃ i₁ i₂ i₃).p₃.op.toLoc).toFunctor.map
        ((F.map (f i₃).op.toLoc).adj.counit.toNatTrans.app (D.obj i₃)) =
      LocallyDiscreteOpToCat.pullHom
        (((F.comp Adj.forget₁).isoMapOfCommSq
          (pbCommSq sq i₁ i₃)).hom.toNatTrans.app
          ((F.map (f i₃).op.toLoc).r.toFunctor.obj (D.obj i₃)))
        (sq₃ i₁ i₂ i₃).p₁₃ (sq₃ i₁ i₂ i₃).p₁ (sq₃ i₁ i₂ i₃).p₃ ≫
      ((F.comp Adj.forget₁).map (sq₃ i₁ i₂ i₃).p₃.op.toLoc).toFunctor.map
        ((F.map (f i₃).op.toLoc).adj.counit.toNatTrans.app (D.obj i₃)) by
    dsimp only [LocallyDiscreteOpToCat.pullHom] at h
    simp only [Category.assoc] at h
    exact h
  -- Now prove h: replace each pullHom(iso.app)(p) with isoMapOfCommSq₃.app
  rw [pullHom_isoMapOfCommSq F sq sq₃ i₁ i₂ i₃,
    pullHom_isoMapOfCommSq' F sq sq₃ i₁ i₂ i₃,
    pullHom_isoMapOfCommSq'' F sq sq₃ i₁ i₂ i₃,
    ← Category.assoc,
    isoMapOfCommSq₃_comp F sq sq₃ i₁ i₂ i₃]

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
