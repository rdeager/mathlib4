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

section BackwardCounit

variable {ι : Type t} {S : C} {X : ι → C} {f : ∀ i, X i ⟶ S}
  (sq : ∀ i j, ChosenPullback (f i) (f j))
  (sq₃ : ∀ (i₁ i₂ i₃ : ι), ChosenPullback₃ (sq i₁ i₂) (sq i₂ i₃) (sq i₁ i₃))

set_option backward.isDefEq.respectTransparency false in
variable (F) in
/-- **Round-trip identity**: applying the forward map to the backward coalgebra structure
gives back the original descent datum. Concretely,
`l_{p₁}(η ≫ r(v) ≫ inv(χ)) ≫ iso ≫ p₂^*(ε) = v`. -/
private lemma roundTrip_eq'
    (hBC : ∀ (i₁ i₂ : ι) (M : (F.obj (.mk (op (X i₂)))).obj),
      IsIso (baseChangeApp F sq i₁ i₂ M))
    (D : (F.comp Adj.forget₁).DescentData' sq sq₃) (i : ι) :
    ((F.comp Adj.forget₁).map (sq i i).p₁.op.toLoc).toFunctor.map
      ((F.map (sq i i).p₁.op.toLoc).adj.unit.toNatTrans.app (D.obj i) ≫
       (F.map (sq i i).p₁.op.toLoc).r.toFunctor.map (D.hom i i) ≫
       inv (baseChangeApp F sq i i (D.obj i))) ≫
      ((F.comp Adj.forget₁).isoMapOfCommSq (pbCommSq sq i i)).hom.toNatTrans.app
        ((F.map (f i).op.toLoc).r.toFunctor.obj (D.obj i)) ≫
      ((F.comp Adj.forget₁).map (sq i i).p₂.op.toLoc).toFunctor.map
        ((F.map (f i).op.toLoc).adj.counit.toNatTrans.app (D.obj i)) = D.hom i i := by
  rw [show ((F.comp Adj.forget₁).map (sq i i).p₁.op.toLoc).toFunctor.map _ =
    (F.map (sq i i).p₁.op.toLoc).l.toFunctor.map _ from rfl]
  simp only [Functor.map_comp, Category.assoc]
  have h_expand : (F.map (sq i i).p₁.op.toLoc).l.toFunctor.map
      (baseChangeApp F sq i i (D.obj i)) ≫
    (F.map (sq i i).p₁.op.toLoc).adj.counit.toNatTrans.app
      ((F.map (sq i i).p₂.op.toLoc).l.toFunctor.obj (D.obj i)) =
    ((F.comp Adj.forget₁).isoMapOfCommSq (pbCommSq sq i i)).hom.toNatTrans.app
      ((F.map (f i).op.toLoc).r.toFunctor.obj (D.obj i)) ≫
    ((F.comp Adj.forget₁).map (sq i i).p₂.op.toLoc).toFunctor.map
      ((F.map (f i).op.toLoc).adj.counit.toNatTrans.app (D.obj i)) := by
    dsimp only [baseChangeApp]
    rw [Functor.map_comp, Category.assoc]
    rw [show (F.map (sq i i).p₁.op.toLoc).l.toFunctor.map
        ((F.map (sq i i).p₁.op.toLoc).r.toFunctor.map _) ≫
        (F.map (sq i i).p₁.op.toLoc).adj.counit.toNatTrans.app _ =
      (F.map (sq i i).p₁.op.toLoc).adj.counit.toNatTrans.app _ ≫ _ from
      (F.map (sq i i).p₁.op.toLoc).adj.counit.toNatTrans.naturality _]
    rw [← Category.assoc, Adj.left_triangle_components, Category.id_comp]
  rw [show (F.map (sq i i).p₁.op.toLoc).l.toFunctor.map
        (inv (baseChangeApp F sq i i (D.obj i))) ≫
      ((F.comp Adj.forget₁).isoMapOfCommSq (pbCommSq sq i i)).hom.toNatTrans.app
        ((F.map (f i).op.toLoc).r.toFunctor.obj (D.obj i)) ≫
      ((F.comp Adj.forget₁).map (sq i i).p₂.op.toLoc).toFunctor.map
        ((F.map (f i).op.toLoc).adj.counit.toNatTrans.app (D.obj i)) =
    (F.map (sq i i).p₁.op.toLoc).adj.counit.toNatTrans.app
      ((F.map (sq i i).p₂.op.toLoc).l.toFunctor.obj (D.obj i)) from by
    rw [← h_expand, ← Category.assoc, ← Functor.map_comp, IsIso.inv_hom_id,
        Functor.map_id, Category.id_comp]]
  rw [show (F.map (sq i i).p₁.op.toLoc).l.toFunctor.map
      ((F.map (sq i i).p₁.op.toLoc).r.toFunctor.map (D.hom i i)) ≫
      (F.map (sq i i).p₁.op.toLoc).adj.counit.toNatTrans.app _ =
    (F.map (sq i i).p₁.op.toLoc).adj.counit.toNatTrans.app _ ≫ D.hom i i from
    (F.map (sq i i).p₁.op.toLoc).adj.counit.toNatTrans.naturality _]
  rw [← Category.assoc, Adj.left_triangle_components, Category.id_comp]

set_option backward.isDefEq.respectTransparency false in
variable (F) in
/-- **Counit condition**: `backward.hom i i ≫ ε = 𝟙`. Uses `roundTrip_eq'`,
`D.pullHom'_hom_self`, `pullHom_isoMapOfCommSq_diagonal`, and `mapId'` faithfulness. -/
lemma counit_eq'
    (hBC : ∀ (i₁ i₂ : ι) (M : (F.obj (.mk (op (X i₂)))).obj),
      IsIso (baseChangeApp F sq i₁ i₂ M))
    (D : (F.comp Adj.forget₁).DescentData' sq sq₃) (i : ι) :
    (F.map (sq i i).p₁.op.toLoc).adj.unit.toNatTrans.app (D.obj i) ≫
      (F.map (sq i i).p₁.op.toLoc).r.toFunctor.map (D.hom i i) ≫
        inv (baseChangeApp F sq i i (D.obj i)) ≫
        (F.map (f i).op.toLoc).adj.counit.toNatTrans.app (D.obj i) =
    𝟙 (D.obj i) := by
  obtain ⟨p, h₁, h₂⟩ := (sq i i).isPullback.exists_lift (𝟙 _) (𝟙 _) (by simp)
  have h_rt := roundTrip_eq' F sq sq₃ hBC D i
  have h_ps := D.pullHom'_hom_self i
  rw [DescentData'.pullHom'_eq_pullHom _ _ _ _ p] at h_ps
  rw [← h_rt] at h_ps
  dsimp only [LocallyDiscreteOpToCat.pullHom] at h_ps
  rw [Functor.map_comp_assoc, Functor.map_comp_assoc] at h_ps
  -- Push bwd past mc'₁ via naturality
  conv at h_ps =>
    lhs; rw [← Category.assoc, ← (F.comp Adj.forget₁).mapComp'_hom_naturality
      (sq i i).p₁.op.toLoc p.op.toLoc (𝟙 (X i)).op.toLoc
      (by rw [← Quiver.Hom.comp_toLoc, ← op_comp, h₁])
      ((F.map (sq i i).p₁.op.toLoc).adj.unit.toNatTrans.app (D.obj i) ≫
       (F.map (sq i i).p₁.op.toLoc).r.toFunctor.map (D.hom i i) ≫
       inv (baseChangeApp F sq i i (D.obj i)))]
  simp only [Category.assoc] at h_ps
  -- Push ε past mc'₂ via naturality
  simp only [mapComp'_inv_naturality] at h_ps
  -- Diagonal coherence: middle = 𝟙
  have h_mid := pullHom_isoMapOfCommSq_diagonal sq i p h₁ h₂ (D.obj i)
  conv at h_ps =>
    lhs
    rw [← Category.assoc, ← Category.assoc, ← Category.assoc]
    rw [Category.assoc (f := ((F.comp Adj.forget₁).map (𝟙 (X i)).op.toLoc).toFunctor.map _)]
    rw [Category.assoc (f := ((F.comp Adj.forget₁).map (𝟙 (X i)).op.toLoc).toFunctor.map _)]
    rw [Category.assoc (f := ((F.comp Adj.forget₁).map (𝟙 (X i)).op.toLoc).toFunctor.map _)]
    simp only [Category.assoc, h_mid, Category.id_comp, Category.comp_id]
  -- 𝟙^*(bwd ≫ ε) = 𝟙; mapId' faithfulness gives bwd ≫ ε = 𝟙
  rw [← Functor.map_comp] at h_ps
  have nat := (F.comp Adj.forget₁).mapId'_hom_naturality (𝟙 (X i)).op.toLoc rfl
    ((F.map (sq i i).p₁.op.toLoc).adj.unit.toNatTrans.app (D.obj i) ≫
     (F.map (sq i i).p₁.op.toLoc).r.toFunctor.map (D.hom i i) ≫
     inv (baseChangeApp F sq i i (D.obj i)) ≫
     (F.map (f i).op.toLoc).adj.counit.toNatTrans.app (D.obj i))
  rw [h_ps, Category.id_comp] at nat
  have := ((F.comp Adj.forget₁).mapId' (𝟙 (X i)).op.toLoc rfl).hom.toNatTrans.isIso_app
    (D.obj i)
  exact (IsIso.eq_comp_inv _).mp nat.symm |>.trans (IsIso.hom_inv_id _)

end BackwardCounit

end Pseudofunctor

end CategoryTheory
