/-
Copyright (c) 2026 Richard Eager. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Richard Eager
-/
module

public import Mathlib.CategoryTheory.Sites.Descent.BenabouRoubaud

/-!
# Bénabou–Roubaud: mates-based helpers

This file provides mates-based helper lemmas for the Bénabou–Roubaud equivalence,
giving cleaner proofs of the key coherence conditions.

## Main results

* `pullHom_isoMapOfCommSq_diagonal`: when the CommSq has equal "top" and "left" maps
  (the diagonal case), pulling back the isoMapOfCommSq along the diagonal lift gives
  the identity. This is the core lemma for `pullHom'_hom_self`.

## Strategy

The key insight is that the `isoMapOfCommSq` for the diagonal pullback square
decomposes through `mapComp'` into two coherence isos that share a common intermediate
(`F.map` of the composed path). After pulling back along the diagonal and applying
the mapComp' associativity, these two isos telescope to the identity.

At the mates level, this corresponds to `conjugateEquiv adj adj (𝟙) = 𝟙`:
both composed paths through the diagonal square give the same morphism, so
the base change is the identity.
-/

@[expose] public section

universe t v' v u' u

namespace CategoryTheory

open Bicategory Opposite Limits

namespace Pseudofunctor

variable {C : Type u} [Category.{v} C]
  {F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Adj Cat.{v', u'}}

section DiagonalCoherence

variable {ι : Type t} {S : C} {X : ι → C} {f : ∀ i, X i ⟶ S}
  (sq : ∀ i j, ChosenPullback (f i) (f j))
  (sq₃ : ∀ (i₁ i₂ i₃ : ι), ChosenPullback₃ (sq i₁ i₂) (sq i₂ i₃) (sq i₁ i₃))

/-- The composed path through the pullback square, used as the common intermediate
for the isoMapOfCommSq decomposition. For the diagonal (i₁ = i₂ = i),
both paths `p₁ ≫ f i` and `p₂ ≫ f i` give this same morphism. -/
noncomputable abbrev composedPathOp (i₁ i₂ : ι) :=
  ((sq i₁ i₂).p₁ ≫ f i₁).op.toLoc

/-- For the diagonal pullback, both composed paths are equal. -/
lemma composedPath_eq (i : ι) :
    ((sq i i).p₁ ≫ f i).op.toLoc = ((sq i i).p₂ ≫ f i).op.toLoc := by
  congr 1; exact congrArg _ (sq i i).condition

set_option backward.isDefEq.respectTransparency false in
/-- **Core diagonal coherence lemma.** When the pullback square is the diagonal
(`i₁ = i₂ = i`), pulling back the `isoMapOfCommSq` along the diagonal lift
gives the identity morphism.

Concretely, for `p : X i ⟶ (sq i i).pullback` with `p ≫ p₁ = 𝟙` and `p ≫ p₂ = 𝟙`,
the composition
```
mapComp'(p₁, p, 𝟙).hom ≫ p*(isoMapOfCommSq.hom.app M) ≫ mapComp'(p₂, p, 𝟙).inv = 𝟙
```
This is the content of `h_mid` in the proof of `pullHom'_hom_self`.

**Proof sketch (mates perspective):** The `isoMapOfCommSq` decomposes as
`mapComp'(fi, p₁, c)⁻¹ ≫ mapComp'(fi, p₂, c)` via `isoMapOfCommSq_eq`,
where `c = fi ≫ p₁ = fi ≫ p₂` is the common composed path.
After pulling back along the diagonal `p`, the two `mapComp'` coherence isos
telescope via `mapComp'₀₁₃_inv_app`, because the 4-object chains
`fi → p₁ → p → 𝟙` and `fi → p₂ → p → 𝟙` both factor through the same
intermediate `fi → 𝟙 = fi`. The resulting pair of inverses cancels. -/
lemma pullHom_isoMapOfCommSq_diagonal
    (i : ι) (p : X i ⟶ (sq i i).pullback)
    (h₁ : p ≫ (sq i i).p₁ = 𝟙 (X i)) (h₂ : p ≫ (sq i i).p₂ = 𝟙 (X i))
    (M : (F.obj (.mk (op (X i)))).obj) :
    ((F.comp Adj.forget₁).mapComp' (sq i i).p₁.op.toLoc p.op.toLoc
      (𝟙 (X i)).op.toLoc (by rw [← Quiver.Hom.comp_toLoc, ← op_comp, h₁])).hom.toNatTrans.app
      ((F.map (f i).op.toLoc).l.toFunctor.obj
        ((F.map (f i).op.toLoc).r.toFunctor.obj M)) ≫
    ((F.comp Adj.forget₁).map p.op.toLoc).toFunctor.map
      (((F.comp Adj.forget₁).isoMapOfCommSq (pbCommSq sq i i)).hom.toNatTrans.app
        ((F.map (f i).op.toLoc).r.toFunctor.obj M)) ≫
    ((F.comp Adj.forget₁).mapComp' (sq i i).p₂.op.toLoc p.op.toLoc
      (𝟙 (X i)).op.toLoc (by rw [← Quiver.Hom.comp_toLoc, ← op_comp, h₂])).inv.toNatTrans.app
      (((F.comp Adj.forget₁).map (f i).op.toLoc).toFunctor.obj
        ((F.map (f i).op.toLoc).r.toFunctor.obj M)) =
    𝟙 _ := by
  -- Decompose isoMapOfCommSq via isoMapOfCommSq_eq
  rw [(F.comp Adj.forget₁).isoMapOfCommSq_eq (pbCommSq sq i i)
    ((sq i i).p₁ ≫ f i).op.toLoc (by rw [← Quiver.Hom.comp_toLoc, ← op_comp])]
  simp only [Iso.trans_hom, Iso.symm_hom, Cat.Hom₂.comp_app]
  rw [Functor.map_comp_assoc]
  -- Now: mc'(p₁,p,𝟙).hom ≫ p*(mc'(fi,p₁,φ).inv) ≫ p*(mc'(fi,p₂,φ).hom) ≫ mc'(p₂,p,𝟙).inv = 𝟙
  -- Insert identity between terms 2 and 3:
  conv_lhs =>
    rw [← Category.assoc, ← Category.assoc]
    rw [Category.assoc (f := ((F.comp Adj.forget₁).mapComp' (sq i i).p₁.op.toLoc p.op.toLoc
      (𝟙 (X i)).op.toLoc _).hom.toNatTrans.app _)]
  set_option backward.isDefEq.respectTransparency false in
  rw [show ((F.comp Adj.forget₁).map p.op.toLoc).toFunctor.map
        (((F.comp Adj.forget₁).mapComp' (f i).op.toLoc (sq i i).p₁.op.toLoc
          ((sq i i).p₁ ≫ f i).op.toLoc _).inv.toNatTrans.app
          ((F.map (f i).op.toLoc).r.toFunctor.obj M)) ≫
      ((F.comp Adj.forget₁).map p.op.toLoc).toFunctor.map
        (((F.comp Adj.forget₁).mapComp' (f i).op.toLoc (sq i i).p₂.op.toLoc
          ((sq i i).p₁ ≫ f i).op.toLoc _).hom.toNatTrans.app
          ((F.map (f i).op.toLoc).r.toFunctor.obj M)) =
    ((F.comp Adj.forget₁).map p.op.toLoc).toFunctor.map
      (((F.comp Adj.forget₁).mapComp' (f i).op.toLoc (sq i i).p₁.op.toLoc
          ((sq i i).p₁ ≫ f i).op.toLoc _).inv.toNatTrans.app
          ((F.map (f i).op.toLoc).r.toFunctor.obj M) ≫
      ((F.comp Adj.forget₁).mapComp' (f i).op.toLoc (sq i i).p₂.op.toLoc
          ((sq i i).p₁ ≫ f i).op.toLoc _).hom.toNatTrans.app
          ((F.map (f i).op.toLoc).r.toFunctor.obj M)) from
    (Functor.map_comp _ _ _).symm]
  -- Cancel epi and mono to expose the telescope
  rw [← cancel_epi (((F.comp Adj.forget₁).mapComp' (sq i i).p₁.op.toLoc p.op.toLoc
    (𝟙 (X i)).op.toLoc (by rw [← Quiver.Hom.comp_toLoc, ← op_comp, h₁])).inv.toNatTrans.app _),
    ← cancel_mono (((F.comp Adj.forget₁).mapComp' (sq i i).p₂.op.toLoc p.op.toLoc
    (𝟙 (X i)).op.toLoc (by rw [← Quiver.Hom.comp_toLoc, ← op_comp, h₂])).hom.toNatTrans.app _)]
  simp only [Category.assoc, ← reassoc_of% Cat.Hom₂.comp_app, Cat.Hom₂.comp_app,
    Iso.inv_hom_id, Cat.Hom₂.id_app, Category.id_comp, Category.comp_id,
    Iso.hom_inv_id]
  -- Cancel the p₂ inv/hom pair
  set_option backward.isDefEq.respectTransparency false in
  erw [Iso.inv_hom_id_app (Cat.Hom.toNatIso
    ((F.comp Adj.forget₁).mapComp' (sq i i).p₂.op.toLoc p.op.toLoc (𝟙 (X i)).op.toLoc
      (by rw [← Quiver.Hom.comp_toLoc, ← op_comp, h₂])))]
  erw [Category.comp_id]
  -- Use mapComp'₀₁₃_inv_app to telescope the remaining terms
  rw [Functor.map_comp]
  have exp₁ := (F.comp Adj.forget₁).mapComp'₀₁₃_inv_app
    (f i).op.toLoc (sq i i).p₁.op.toLoc p.op.toLoc
    ((sq i i).p₁ ≫ f i).op.toLoc (𝟙 (X i)).op.toLoc (f i).op.toLoc
    (by rw [← Quiver.Hom.comp_toLoc, ← op_comp])
    (by rw [← Quiver.Hom.comp_toLoc, ← op_comp, h₁])
    (by rw [← Quiver.Hom.comp_toLoc, ← op_comp, Category.id_comp])
    ((F.map (f i).op.toLoc).r.toFunctor.obj M)
  have exp₂ := (F.comp Adj.forget₁).mapComp'₀₁₃_inv_app
    (f i).op.toLoc (sq i i).p₂.op.toLoc p.op.toLoc
    ((sq i i).p₁ ≫ f i).op.toLoc (𝟙 (X i)).op.toLoc (f i).op.toLoc
    (by rw [← Quiver.Hom.comp_toLoc, ← op_comp, (sq i i).condition.symm])
    (by rw [← Quiver.Hom.comp_toLoc, ← op_comp, h₂])
    (by rw [← Quiver.Hom.comp_toLoc, ← op_comp, Category.id_comp])
    ((F.map (f i).op.toLoc).r.toFunctor.obj M)
  -- From exp₁ and exp₂ (same LHS, same tail): cancel the common tail
  have h_eq := exp₁.symm.trans exp₂
  have h_cleaned := congr_arg (· ≫ ((F.comp Adj.forget₁).mapComp' ((sq i i).p₁ ≫ f i).op.toLoc
    p.op.toLoc (f i).op.toLoc
    (by rw [← Quiver.Hom.comp_toLoc, ← op_comp, ← Category.assoc, h₁,
            Category.id_comp])).hom.toNatTrans.app
    ((F.map (f i).op.toLoc).r.toFunctor.obj M)) h_eq
  simp only [Category.assoc] at h_cleaned
  set_option backward.isDefEq.respectTransparency false in
  erw [Iso.inv_hom_id_app (Cat.Hom.toNatIso ((F.comp Adj.forget₁).mapComp'
    ((sq i i).p₁ ≫ f i).op.toLoc p.op.toLoc (f i).op.toLoc
    (by rw [← Quiver.Hom.comp_toLoc, ← op_comp, ← Category.assoc, h₁,
            Category.id_comp])))] at h_cleaned
  erw [Category.comp_id, Category.comp_id] at h_cleaned
  -- h_cleaned: α₁.hom ≫ pp*(inv₁) = α₂.hom ≫ pp*(inv₂)
  rw [← cancel_epi (((F.comp Adj.forget₁).mapComp' (sq i i).p₁.op.toLoc p.op.toLoc
    (𝟙 (X i)).op.toLoc (by rw [← Quiver.Hom.comp_toLoc, ← op_comp, h₁])).hom.toNatTrans.app
    (((F.comp Adj.forget₁).map (f i).op.toLoc).toFunctor.obj
      ((F.map (f i).op.toLoc).r.toFunctor.obj M)))]
  simp only [← Category.assoc]
  rw [h_cleaned]
  simp only [Category.assoc, ← Functor.map_comp]
  set_option backward.isDefEq.respectTransparency false in
  erw [Iso.inv_hom_id_app (Cat.Hom.toNatIso ((F.comp Adj.forget₁).mapComp'
    (f i).op.toLoc (sq i i).p₂.op.toLoc ((sq i i).p₁ ≫ f i).op.toLoc
    (by rw [← Quiver.Hom.comp_toLoc, ← op_comp, (sq i i).condition.symm])))]
  erw [Functor.map_id, Category.comp_id]
  rw [show ((F.comp Adj.forget₁).mapComp' (sq i i).p₁.op.toLoc p.op.toLoc
        (𝟙 (X i)).op.toLoc _).inv.toNatTrans.app
        ((F.map (f i).op.toLoc).l.toFunctor.obj
          ((F.map (f i).op.toLoc).r.toFunctor.obj M)) =
      ((F.comp Adj.forget₁).mapComp' (sq i i).p₁.op.toLoc p.op.toLoc
        (𝟙 (X i)).op.toLoc _).inv.toNatTrans.app
        (((F.comp Adj.forget₁).map (f i).op.toLoc).toFunctor.obj
          ((F.map (f i).op.toLoc).r.toFunctor.obj M)) from rfl]
  simp only [Category.assoc, ← reassoc_of% Cat.Hom₂.comp_app, Cat.Hom₂.comp_app,
    Iso.hom_inv_id, Cat.Hom₂.id_app, Category.id_comp]

end DiagonalCoherence

section CleanForward

variable {ι : Type t} {S : C} {X : ι → C} {f : ∀ i, X i ⟶ S}
  (sq : ∀ i j, ChosenPullback (f i) (f j))
  (sq₃ : ∀ (i₁ i₂ i₃ : ι), ChosenPullback₃ (sq i₁ i₂) (sq i₂ i₃) (sq i₁ i₃))

set_option backward.isDefEq.respectTransparency false in
variable (F) in
/-- Clean proof of the unit condition for the forward functor, using
`pullHom_isoMapOfCommSq_diagonal` to handle the coherence. This replaces
the 220-line inline proof in `BenabouRoubaud.lean`.

The unit condition states that pulling back the descent datum `hom i i` along
the diagonal gives the identity. The proof reduces to:
1. Push `D.hom` and `ε` past the `pullHom` coherence wrappers (naturality)
2. Apply `pullHom_isoMapOfCommSq_diagonal` to show the middle isoMapOfCommSq term = 𝟙
3. Conclude by the coalgebra counit `D.hom i i ≫ ε = 𝟙`. -/
noncomputable def DescentDataAsCoalgebra.toDescentData'Obj_v2
    (D : F.DescentDataAsCoalgebra f) :
    (F.comp Adj.forget₁).DescentData' sq sq₃ where
  obj := D.obj
  hom i₁ i₂ :=
    ((F.comp Adj.forget₁).map (sq i₁ i₂).p₁.op.toLoc).toFunctor.map (D.hom i₁ i₂) ≫
    ((F.comp Adj.forget₁).isoMapOfCommSq (pbCommSq sq i₁ i₂)).hom.toNatTrans.app
      ((F.map (f i₂).op.toLoc).r.toFunctor.obj (D.obj i₂)) ≫
    ((F.comp Adj.forget₁).map (sq i₁ i₂).p₂.op.toLoc).toFunctor.map
      ((F.map (f i₂).op.toLoc).adj.counit.toNatTrans.app (D.obj i₂))
  pullHom'_hom_self i := by
    obtain ⟨p, h₁, h₂⟩ := (sq i i).isPullback.exists_lift (𝟙 _) (𝟙 _) (by simp)
    rw [DescentData'.pullHom'_eq_pullHom _ _ _ _ p]
    dsimp only [LocallyDiscreteOpToCat.pullHom]
    rw [Functor.map_comp_assoc, Functor.map_comp_assoc]
    -- Push D.hom past the outer mapComp' using naturality
    set_option backward.isDefEq.respectTransparency false in
    conv_lhs =>
      rw [← Category.assoc, ← (F.comp Adj.forget₁).mapComp'_hom_naturality
        (sq i i).p₁.op.toLoc p.op.toLoc (𝟙 (X i)).op.toLoc
        (by rw [← Quiver.Hom.comp_toLoc, ← op_comp, h₁]) (D.hom i i)]
    simp only [Category.assoc]
    -- Push ε past the outer mapComp' using naturality
    set_option backward.isDefEq.respectTransparency false in
    simp only [mapComp'_inv_naturality]
    -- Now: 𝟙*(D.hom) ≫ [middle = pullHom(iso)(p)] ≫ 𝟙*(ε) = 𝟙
    -- The middle is pullHom_isoMapOfCommSq_diagonal
    suffices h_mid :
        ((F.comp Adj.forget₁).mapComp' (sq i i).p₁.op.toLoc p.op.toLoc
          (𝟙 (X i)).op.toLoc (by rw [← Quiver.Hom.comp_toLoc, ← op_comp, h₁])).hom.toNatTrans.app
          ((F.map (f i).op.toLoc).l.toFunctor.obj
            ((F.map (f i).op.toLoc).r.toFunctor.obj (D.obj i))) ≫
        ((F.comp Adj.forget₁).map p.op.toLoc).toFunctor.map
          (((F.comp Adj.forget₁).isoMapOfCommSq (pbCommSq sq i i)).hom.toNatTrans.app
            ((F.map (f i).op.toLoc).r.toFunctor.obj (D.obj i))) ≫
        ((F.comp Adj.forget₁).mapComp' (sq i i).p₂.op.toLoc p.op.toLoc
          (𝟙 (X i)).op.toLoc (by rw [← Quiver.Hom.comp_toLoc, ← op_comp, h₂])).inv.toNatTrans.app
          (((F.comp Adj.forget₁).map (f i).op.toLoc).toFunctor.obj
            ((F.map (f i).op.toLoc).r.toFunctor.obj (D.obj i))) =
        𝟙 _ by
      conv_lhs =>
        rw [← Category.assoc, ← Category.assoc, ← Category.assoc]
        rw [Category.assoc (f := ((F.comp Adj.forget₁).map (𝟙 (X i)).op.toLoc).toFunctor.map _)]
        rw [Category.assoc (f := ((F.comp Adj.forget₁).map (𝟙 (X i)).op.toLoc).toFunctor.map _)]
        rw [Category.assoc (f := ((F.comp Adj.forget₁).map (𝟙 (X i)).op.toLoc).toFunctor.map _)]
        simp only [Category.assoc, h_mid, Category.id_comp, Category.comp_id]
      rw [← Functor.map_comp, D.counit, Functor.map_id]
    -- Apply the extracted diagonal coherence lemma
    exact pullHom_isoMapOfCommSq_diagonal sq i p h₁ h₂ (D.obj i)
  pullHom'_hom_comp i₁ i₂ i₃ := by
    sorry

set_option backward.isDefEq.respectTransparency false in
variable (F) in
/-- The v2 construction produces the same descent data as the original. -/
lemma toDescentData'Obj_v2_eq
    (D : F.DescentDataAsCoalgebra f) :
    DescentDataAsCoalgebra.toDescentData'Obj_v2 F sq sq₃ D =
    DescentDataAsCoalgebra.toDescentData'Obj F sq sq₃ D := by
  rfl

end CleanForward

end Pseudofunctor

end CategoryTheory
