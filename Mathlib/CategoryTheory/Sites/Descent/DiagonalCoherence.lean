/-
Copyright (c) 2026 Richard Eager. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Richard Eager
-/
module

public import Mathlib.CategoryTheory.Sites.Descent.DescentDataAsCoalgebra
public import Mathlib.CategoryTheory.Sites.Descent.DescentDataPrime

/-!
# Diagonal coherence for pullback squares

When a pseudofunctor `F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Adj Cat` is applied to the
diagonal pullback square (i.e., `i₁ = i₂ = i`), pulling back the
`isoMapOfCommSq` coherence isomorphism along the diagonal lift gives the identity.

This is the core coherence lemma needed for both `pullHom'_hom_self` (forward
direction of Bénabou–Roubaud) and the counit condition (backward direction).

## Main results

* `pbCommSq`: the pullback condition as a `CommSq` in `LocallyDiscrete Cᵒᵖ`
* `composedPath_eq`: both composed paths through the diagonal square are equal
* `pullHom_isoMapOfCommSq_diagonal`: the diagonal pullback of `isoMapOfCommSq` is `𝟙`

## References

* [J. Bénabou, J. Roubaud, *Monades et descente*,
  C. R. Acad. Sc. Paris, t. 270, 1970][benabou-roubaud-1970]
* [B. Kahn, *Descente galoisienne et isogénies*, arXiv:2404.00868][kahn-2024]
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

/-! ### Pullback commutative squares

The pullback condition `p₁ ≫ f i₁ = p₂ ≫ f i₂` lifts to a commutative square
in `LocallyDiscrete Cᵒᵖ`, which can be fed to `Pseudofunctor.isoMapOfCommSq`. -/

/-- The pullback condition for `sq i₁ i₂` as a `CommSq` in `LocallyDiscrete Cᵒᵖ`.
This encodes the commutativity of the pullback square, lifted to the opposite category. -/
def pbCommSq (i₁ i₂ : ι) : CommSq (f i₁).op.toLoc (f i₂).op.toLoc
    (sq i₁ i₂).p₁.op.toLoc (sq i₁ i₂).p₂.op.toLoc := by
  constructor
  change ((sq i₁ i₂).p₁ ≫ f i₁).op.toLoc = ((sq i₁ i₂).p₂ ≫ f i₂).op.toLoc
  rw [(sq i₁ i₂).condition]

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
  rw [(F.comp Adj.forget₁).isoMapOfCommSq_eq (pbCommSq sq i i)
    ((sq i i).p₁ ≫ f i).op.toLoc (by rw [← Quiver.Hom.comp_toLoc, ← op_comp])]
  simp only [Iso.trans_hom, Iso.symm_hom, Cat.Hom₂.comp_app]
  rw [Functor.map_comp_assoc]
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
  rw [← cancel_epi (((F.comp Adj.forget₁).mapComp' (sq i i).p₁.op.toLoc p.op.toLoc
    (𝟙 (X i)).op.toLoc (by rw [← Quiver.Hom.comp_toLoc, ← op_comp, h₁])).inv.toNatTrans.app _),
    ← cancel_mono (((F.comp Adj.forget₁).mapComp' (sq i i).p₂.op.toLoc p.op.toLoc
    (𝟙 (X i)).op.toLoc (by rw [← Quiver.Hom.comp_toLoc, ← op_comp, h₂])).hom.toNatTrans.app _)]
  simp only [Category.assoc, ← reassoc_of% Cat.Hom₂.comp_app, Cat.Hom₂.comp_app,
    Iso.inv_hom_id, Cat.Hom₂.id_app, Category.id_comp, Category.comp_id,
    Iso.hom_inv_id]
  set_option backward.isDefEq.respectTransparency false in
  erw [Iso.inv_hom_id_app (Cat.Hom.toNatIso
    ((F.comp Adj.forget₁).mapComp' (sq i i).p₂.op.toLoc p.op.toLoc (𝟙 (X i)).op.toLoc
      (by rw [← Quiver.Hom.comp_toLoc, ← op_comp, h₂])))]
  erw [Category.comp_id]
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

end Pseudofunctor

end CategoryTheory
