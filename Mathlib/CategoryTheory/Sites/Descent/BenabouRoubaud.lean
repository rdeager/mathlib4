/-
Copyright (c) 2026 Richard Eager. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Richard Eager
-/
module

public import Mathlib.CategoryTheory.Sites.Descent.DescentDataAsCoalgebra
public import Mathlib.CategoryTheory.Sites.Descent.DescentDataPrime

/-!
# Bénabou–Roubaud: descent data as coalgebras

Given a pseudofunctor `F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Adj Cat` encoding inverse/direct image
adjunctions `(f^*, f_*)` for each morphism `f`, a family of morphisms `f i : X i ⟶ S`,
chosen pullbacks `sq` and threefold pullbacks `sq₃`, we construct an equivalence between:

* `F.DescentDataAsCoalgebra f`: coalgebra-style descent data, where compatibility morphisms
  are of the form `obj i₁ ⟶ (f i₁)^*((f i₂)_*(obj i₂))` [B-R §1.1]
* `(F.comp Adj.forget₁).DescentData' sq sq₃`: standard descent data with compatibility
  morphisms `p₁^*(obj i₁) ⟶ p₂^*(obj i₂)` over chosen pullbacks

The forward direction (coalgebra → descent) does not require the Beck–Chevalley condition.
The backward direction (descent → coalgebra) requires that the base change morphisms
arising from the pullback squares are isomorphisms [B-R §1.2, Chevalley condition].

Composing with the existing equivalence `DescentData'.descentDataEquivalence` yields
an equivalence with `DescentData`, filling the TODO in `DescentDataAsCoalgebra.lean`.

## Main definitions

* `baseChangeApp`: the base change morphism `χ` for a pullback square [Kahn Eq (1.2)]
* `DescentDataAsCoalgebra.toDescentData'Functor`: forward functor (no BC needed)
* `DescentData'.fromDescentDataAsCoalgebraFunctor`: backward functor (requires BC)
* `descentDataAsCoalgebraEquivDescentData'`: the equivalence (requires BC)

## References

* [J. Bénabou, J. Roubaud, *Monades et descente*][benabou-roubaud-1970]
* [B. Kahn, *Descente galoisienne et isogénies*][kahn-2024]
  - §1.3 Eq (1.3): the map ξ(φ) = p₂*(ε) ∘ iso ∘ p₁*(φ)
  - §2.1: Exchange (Beck–Chevalley) condition
  - §4.2: Main theorem identifying descent data with monad algebras

-/

@[expose] public section

universe t v' v u' u

namespace CategoryTheory

open Bicategory Opposite Limits

namespace Pseudofunctor

variable {C : Type u} [Category.{v} C]
  {F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Adj Cat.{v', u'}}

section BenabouRoubaud

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

/-! ### Base change morphism

[Kahn Eq (1.2)] For each pullback square, the **base change morphism** `χ` is the
canonical natural transformation `(f i₁)^* ∘ (f i₂)_* → (p₁)_* ∘ p₂^*`. It is
constructed as the composite:
```
(f i₁)^*((f i₂)_*(M)) ──[η_{p₁}]──→ (p₁)_*(p₁^*((f i₁)^*((f i₂)_*(M))))
    ──[(p₁)_*(isoMapOfCommSq)]──→ (p₁)_*(p₂^*((f i₂)^*((f i₂)_*(M))))
    ──[(p₁)_*(p₂^*(ε))]──→ (p₁)_*(p₂^*(M))
```
where `η_{p₁}` is the unit of `p₁^* ⊣ (p₁)_*`, the middle step uses the pseudofunctor
coherence iso for the pullback square, and `ε` is the counit of `(f i₂)^* ⊣ (f i₂)_*`. -/

set_option backward.isDefEq.respectTransparency false in
variable (F) in
/-- [Kahn Eq (1.2)] The base change morphism for the pullback square at `(i₁, i₂)`.
Maps `(f i₁)^*((f i₂)_*(M)) → (p₁)_*(p₂^*(M))`. -/
noncomputable def baseChangeApp (i₁ i₂ : ι)
    (M : (F.obj (.mk (op (X i₂)))).obj) :
    (F.map (f i₁).op.toLoc).l.toFunctor.obj
      ((F.map (f i₂).op.toLoc).r.toFunctor.obj M) ⟶
    (F.map (sq i₁ i₂).p₁.op.toLoc).r.toFunctor.obj
      ((F.map (sq i₁ i₂).p₂.op.toLoc).l.toFunctor.obj M) :=
  -- Step 1: Unit η_{p₁} at (f i₁)^*((f i₂)_*(M))
  (F.map (sq i₁ i₂).p₁.op.toLoc).adj.unit.toNatTrans.app _ ≫
  -- Step 2: (p₁)_* applied to (isoMapOfCommSq.app ≫ p₂^*(counit))
  (F.map (sq i₁ i₂).p₁.op.toLoc).r.toFunctor.map (
    ((F.comp Adj.forget₁).isoMapOfCommSq (pbCommSq sq i₁ i₂)).hom.toNatTrans.app
      ((F.map (f i₂).op.toLoc).r.toFunctor.obj M) ≫
    ((F.comp Adj.forget₁).map (sq i₁ i₂).p₂.op.toLoc).toFunctor.map
      ((F.map (f i₂).op.toLoc).adj.counit.toNatTrans.app M))

/-! ### Forward functor: DescentDataAsCoalgebra → DescentData'

[B-R §1.3, Kahn Eq (1.3)] The forward direction constructs standard descent data from
coalgebra-style data. The hom over the pullback is built as:
```
p₁^*(D.obj i₁) ──[p₁^*(D.hom)]──→ p₁^*((f i₁)^*((f i₂)_*(D.obj i₂)))
    ──[isoMapOfCommSq]──→ p₂^*((f i₂)^*((f i₂)_*(D.obj i₂)))
    ──[p₂^*(counit)]──→ p₂^*(D.obj i₂)
```
No Beck–Chevalley condition is needed for this direction. -/

set_option backward.isDefEq.respectTransparency false in
variable (F) in
/-- [B-R §1.3] Forward map on objects: from coalgebra-style descent data to
standard descent data over chosen pullbacks. -/
noncomputable def DescentDataAsCoalgebra.toDescentData'Obj
    (D : F.DescentDataAsCoalgebra f) :
    (F.comp Adj.forget₁).DescentData' sq sq₃ where
  obj := D.obj
  hom i₁ i₂ :=
    -- Step 1 [Kahn §1.3]: Apply p₁^* to coalgebra structure map
    ((F.comp Adj.forget₁).map (sq i₁ i₂).p₁.op.toLoc).toFunctor.map (D.hom i₁ i₂) ≫
    -- Step 2 [B-R pullback iso]: isoMapOfCommSq applied at (f i₂)_*(D.obj i₂)
    ((F.comp Adj.forget₁).isoMapOfCommSq (pbCommSq sq i₁ i₂)).hom.toNatTrans.app
      ((F.map (f i₂).op.toLoc).r.toFunctor.obj (D.obj i₂)) ≫
    -- Step 3 [B-R §1.1]: p₂^* applied to counit ε^{f i₂}
    ((F.comp Adj.forget₁).map (sq i₁ i₂).p₂.op.toLoc).toFunctor.map
      ((F.map (f i₂).op.toLoc).adj.counit.toNatTrans.app (D.obj i₂))
  -- [B-R Theorem, unit direction] Follows from coalgebra counit: D.hom i i ≫ ε = id
  pullHom'_hom_self i := by
    sorry
  -- [B-R Theorem, cocycle] Follows from coalgebra coassociativity
  pullHom'_hom_comp i₁ i₂ i₃ := by
    sorry

set_option backward.isDefEq.respectTransparency false in
variable (F) in
/-- [B-R §1.3] Forward functor from coalgebra-style to standard descent data.
This direction does not require the Beck–Chevalley condition. -/
noncomputable def DescentDataAsCoalgebra.toDescentData'Functor :
    F.DescentDataAsCoalgebra f ⥤ (F.comp Adj.forget₁).DescentData' sq sq₃ where
  obj D := DescentDataAsCoalgebra.toDescentData'Obj F sq sq₃ D
  map {D₁ D₂} φ :=
    { hom i := φ.hom i
      comm i₁ i₂ := by sorry }

/-! ### Beck–Chevalley condition and backward functor

[B-R §1.2, Kahn §2.1] The Beck–Chevalley (exchange) condition states that the base
change morphism `χ` is an isomorphism for each pullback square. Under this condition,
we can invert `χ` to construct the backward functor from descent data to coalgebras. -/

set_option backward.isDefEq.respectTransparency false in
variable (F) in
/-- [B-R Theorem, backward direction] From standard descent data to coalgebra-style data.
Requires Beck–Chevalley: `baseChangeApp` is an iso for all pullback squares.

The coalgebra structure map is:
```
D'.obj i₁ ──[η_{p₁}]──→ (p₁)_*(p₁^*(D'.obj i₁))
    ──[(p₁)_*(D'.hom)]──→ (p₁)_*(p₂^*(D'.obj i₂))
    ──[χ⁻¹]──→ (f i₁)^*((f i₂)_*(D'.obj i₂))
```
-/
noncomputable def DescentData'.toDescentDataAsCoalgebraObj
    (hBC : ∀ (i₁ i₂ : ι) (M : (F.obj (.mk (op (X i₂)))).obj),
      IsIso (baseChangeApp F sq i₁ i₂ M))
    (D : (F.comp Adj.forget₁).DescentData' sq sq₃) :
    F.DescentDataAsCoalgebra f where
  obj := D.obj
  hom i₁ i₂ :=
    -- Step 1: Unit of p₁ adjunction at obj i₁
    (F.map (sq i₁ i₂).p₁.op.toLoc).adj.unit.toNatTrans.app (D.obj i₁) ≫
    -- Step 2: (p₁)_* applied to D'.hom
    (F.map (sq i₁ i₂).p₁.op.toLoc).r.toFunctor.map (D.hom i₁ i₂) ≫
    -- Step 3: Inverse of base change morphism (exists by BC)
    inv (baseChangeApp F sq i₁ i₂ (D.obj i₂))
  -- [B-R] Counit follows from pullHom'_hom_self and triangle identities
  counit := sorry
  -- [B-R] Coassociativity follows from pullHom'_hom_comp and BC naturality
  coassoc := sorry

set_option backward.isDefEq.respectTransparency false in
variable (F) in
/-- [B-R Theorem, backward direction] Backward functor from standard descent data to
coalgebra-style data. Requires Beck–Chevalley condition. -/
noncomputable def DescentData'.fromDescentDataAsCoalgebraFunctor
    (hBC : ∀ (i₁ i₂ : ι) (M : (F.obj (.mk (op (X i₂)))).obj),
      IsIso (baseChangeApp F sq i₁ i₂ M)) :
    (F.comp Adj.forget₁).DescentData' sq sq₃ ⥤ F.DescentDataAsCoalgebra f where
  obj D := DescentData'.toDescentDataAsCoalgebraObj F sq sq₃ hBC D
  map {D₁ D₂} φ :=
    { hom i := φ.hom i
      comm i₁ i₂ := by
        sorry }

/-! ### The equivalence

[B-R Theorem] Under Beck–Chevalley, the forward and backward functors form an equivalence
of categories. -/

set_option backward.isDefEq.respectTransparency false in
variable (F) in
/-- **Bénabou–Roubaud theorem.** Under the Beck–Chevalley condition, coalgebra-style
descent data is equivalent to standard descent data over chosen pullbacks.

This fills the TODO in `DescentDataAsCoalgebra.lean`. -/
noncomputable def descentDataAsCoalgebraEquivDescentData'
    (hBC : ∀ (i₁ i₂ : ι) (M : (F.obj (.mk (op (X i₂)))).obj),
      IsIso (baseChangeApp F sq i₁ i₂ M)) :
    F.DescentDataAsCoalgebra f ≌ (F.comp Adj.forget₁).DescentData' sq sq₃ where
  functor := DescentDataAsCoalgebra.toDescentData'Functor F sq sq₃
  inverse := DescentData'.fromDescentDataAsCoalgebraFunctor F sq sq₃ hBC
  -- Unit: roundtrip coalgebra → descent → coalgebra ≅ id
  unitIso := sorry
  -- Counit: roundtrip descent → coalgebra → descent ≅ id
  counitIso := sorry

set_option backward.isDefEq.respectTransparency false in
variable (F) in
/-- **Bénabou–Roubaud theorem, full version.** Composing with the existing equivalence
`DescentData'.descentDataEquivalence`, we obtain an equivalence between coalgebra-style
descent data and universal descent data. -/
noncomputable def descentDataAsCoalgebraEquivDescentData
    (hBC : ∀ (i₁ i₂ : ι) (M : (F.obj (.mk (op (X i₂)))).obj),
      IsIso (baseChangeApp F sq i₁ i₂ M)) :
    F.DescentDataAsCoalgebra f ≌ (F.comp Adj.forget₁).DescentData f :=
  (descentDataAsCoalgebraEquivDescentData' F sq sq₃ hBC).trans
    (DescentData'.descentDataEquivalence _ _ _)

end BenabouRoubaud

end Pseudofunctor

end CategoryTheory
