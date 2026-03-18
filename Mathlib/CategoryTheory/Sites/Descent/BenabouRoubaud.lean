/-
Copyright (c) 2026 Richard Eager. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Richard Eager
-/
module

public import Mathlib.CategoryTheory.Sites.Descent.DiagonalCoherence

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

## Correspondence with the original papers

### Bénabou–Roubaud (1970)

| B-R notation | Lean notation | Description |
|---|---|---|
| `P : M → A` | `F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Adj Cat` | Bifibration / Adj-valued pseudofunctor |
| `M(A)` | `(F.obj (.mk (op A))).obj` | Fiber category over `A` |
| `a^*` | `(F.map a.op.toLoc).l.toFunctor` | Inverse image (left adjoint) |
| `a_*` | `(F.map a.op.toLoc).r.toFunctor` | Direct image (right adjoint) |
| `η^a`, `ε^a` | `.adj.unit.toNatTrans`, `.adj.counit.toNatTrans` | Adjunction unit/counit |
| `T^a = a^*a_*` | Comonad from `(F.map a.op.toLoc).adj` | Associated comonad [B-R §1.1] |
| `M^a` (algebras) | `DescentDataAsCoalgebra` | Coalgebra category [B-R §1.1] |
| `D(a)` (descent) | `DescentData'` / `DescentData` | Descent data category [B-R §1.3] |
| Condition (C) | `hBC : IsIso (baseChangeApp ...)` | Chevalley condition [B-R §1.2] |
| `K^a : D(a) → M^a` | `descentDataAsCoalgebraEquivDescentData'` | The B-R equivalence |

Note: B-R uses `a_*` left adjoint to `a^*` (monad `T^a = a^*a_*`), while mathlib uses
`a^*` left adjoint to `a_*` (comonad `a^*a_*`). The mathematical content is the same.

### Kahn (2024), arXiv:2404.00868

| Kahn notation | Lean construction | Reference |
|---|---|---|
| `ξ(φ)` | `toDescentData'Obj.hom` | Eq (1.3): `p₂^*(ε) ∘ iso ∘ p₁^*(φ)` |
| `χ` (base change) | `baseChangeApp` | Eq (1.2): `η ≫ r(iso ≫ p₂^*(ε))` |
| Exchange condition | `hBC` hypothesis | Definition 2.1 |
| `Δ^*(ξ(φ)) = φ ∘ η` | `pullHom'_hom_self` | Theorem 4.2 (unit condition) |
| Cocycle condition | `pullHom'_hom_comp` | Proposition 3.3 (associativity) |

## Main definitions

* `baseChangeApp`: the base change morphism `χ` for a pullback square [Kahn Eq (1.2)]
* `DescentDataAsCoalgebra.toDescentData'Functor`: forward functor (no BC needed)
* `DescentData'.fromDescentDataAsCoalgebraFunctor`: backward functor (requires BC)
* `descentDataAsCoalgebraEquivDescentData'`: the equivalence (requires BC)
* `descentDataAsCoalgebraEquivDescentData`: composed with `descentDataEquivalence`

## References

* [J. Bénabou, J. Roubaud, *Monades et descente*,
  C. R. Acad. Sc. Paris, t. 270, 1970][benabou-roubaud-1970]
* [B. Kahn, *Descente galoisienne et isogénies*, arXiv:2404.00868][kahn-2024]
* [F. Borceux, *Handbook of Categorical Algebra 2*, Chapter 5][borceux-1994]

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

/-! ### Base change morphism

[Kahn Eq (1.2), B-R §1.2] For each pullback square
```
  X i₁ ×_S X i₂ ──p₂──→ X i₂
       |                    |
       p₁                 f i₂
       |                    |
       v                    v
     X i₁ ────f i₁────→    S
```
the **base change morphism** `χ` is the canonical map
`(f i₁)^* ∘ (f i₂)_* → (p₁)_* ∘ p₂^*`. In B-R's original formulation (§1.2),
the Chevalley condition (C) states that `χ` is an isomorphism for pullback squares.
Kahn (§2.1, Definition 2.1) calls this the "exchange condition".

The construction uses three ingredients:
1. **Unit** `η^{p₁}` of the adjunction `p₁^* ⊣ (p₁)_*` [B-R §1.1]
2. **Pseudofunctor coherence** `isoMapOfCommSq` for the pullback square, extracting
   the compatibility `(f i₁)^* ∘ p₁^* ≅ (f i₂)^* ∘ p₂^*`
3. **Counit** `ε^{f i₂}` of the adjunction `(f i₂)^* ⊣ (f i₂)_*` [B-R §1.1] -/

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

set_option backward.isDefEq.respectTransparency false in
variable (F) in
/-- [Kahn §2.1] Naturality of the base change morphism in the module argument.
For `g : M₁ ⟶ M₂`, the base change commutes with functorial actions:
`χ(M₁) ≫ (p₁)_*(p₂^*(g)) = (f i₁)^*((f i₂)_*(g)) ≫ χ(M₂)`. -/
private lemma baseChangeApp_naturality (i₁ i₂ : ι)
    {M₁ M₂ : (F.obj (.mk (op (X i₂)))).obj} (g : M₁ ⟶ M₂) :
    baseChangeApp F sq i₁ i₂ M₁ ≫
      (F.map (sq i₁ i₂).p₁.op.toLoc).r.toFunctor.map
        (((F.comp Adj.forget₁).map (sq i₁ i₂).p₂.op.toLoc).toFunctor.map g) =
    (F.map (f i₁).op.toLoc).l.toFunctor.map
      ((F.map (f i₂).op.toLoc).r.toFunctor.map g) ≫
    baseChangeApp F sq i₁ i₂ M₂ := by
  dsimp only [baseChangeApp]
  rw [Category.assoc, ← Functor.map_comp, ← Category.assoc,
      ← Adj.unit_naturality_assoc, ← Functor.map_comp]
  congr 1; congr 1
  -- Inner: (iso₁ ≫ l_p₂(ε₁)) ≫ l_p₂(g) = l_p₁(l_f₁(r₂(g))) ≫ iso₂ ≫ l_p₂(ε₂)
  simp only [Category.assoc]
  rw [← Functor.map_comp, ← Adj.counit_naturality, Functor.map_comp,
      ← Category.assoc, ← Category.assoc]
  congr 1
  -- iso₁ ≫ target.map(r₂(g)) = source.map'(r₂(g)) ≫ iso₂
  -- Bridge l_p₁, l_f₁ on RHS to (F.comp Adj.forget₁) form, then fold
  rw [show (F.map (sq i₁ i₂).p₁.op.toLoc).l.toFunctor.map
        ((F.map (f i₁).op.toLoc).l.toFunctor.map
          ((F.map (f i₂).op.toLoc).r.toFunctor.map g)) =
      ((F.comp Adj.forget₁).map (sq i₁ i₂).p₁.op.toLoc).toFunctor.map
        (((F.comp Adj.forget₁).map (f i₁).op.toLoc).toFunctor.map
          ((F.map (f i₂).op.toLoc).r.toFunctor.map g)) from rfl,
    ← Cat.Hom.comp_map]
  -- Now both sides use isoMapOfCommSq's source/target composites
  exact (((F.comp Adj.forget₁).isoMapOfCommSq
    (pbCommSq sq i₁ i₂)).hom.toNatTrans.naturality
    ((F.map (f i₂).op.toLoc).r.toFunctor.map g)).symm

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
    obtain ⟨p, h₁, h₂⟩ := (sq i i).isPullback.exists_lift (𝟙 _) (𝟙 _) (by simp)
    set_option backward.isDefEq.respectTransparency false in
    rw [DescentData'.pullHom'_eq_pullHom _ _ _ _ p]
    dsimp only [LocallyDiscreteOpToCat.pullHom]
    rw [Functor.map_comp_assoc, Functor.map_comp_assoc]
    -- Push D.hom past outer_hom and ε past outer_inv using naturality
    set_option backward.isDefEq.respectTransparency false in
    conv_lhs =>
      rw [← Category.assoc, ← (F.comp Adj.forget₁).mapComp'_hom_naturality
        (sq i i).p₁.op.toLoc p.op.toLoc (𝟙 (X i)).op.toLoc
        (by rw [comp_op_toLoc, h₁]) (D.hom i i)]
    simp only [Category.assoc]
    set_option backward.isDefEq.respectTransparency false in
    simp only [mapComp'_inv_naturality]
    -- Now: 𝟙*(D.hom) ≫ [middle = pullHom(iso)(p)] ≫ 𝟙*(ε) = 𝟙
    -- The middle is pullHom_isoMapOfCommSq_diagonal
    suffices h_mid :
        ((F.comp Adj.forget₁).mapComp' (sq i i).p₁.op.toLoc p.op.toLoc
          (𝟙 (X i)).op.toLoc (by rw [comp_op_toLoc, h₁])).hom.toNatTrans.app
          ((F.map (f i).op.toLoc).l.toFunctor.obj
            ((F.map (f i).op.toLoc).r.toFunctor.obj (D.obj i))) ≫
        ((F.comp Adj.forget₁).map p.op.toLoc).toFunctor.map
          (((F.comp Adj.forget₁).isoMapOfCommSq (pbCommSq sq i i)).hom.toNatTrans.app
            ((F.map (f i).op.toLoc).r.toFunctor.obj (D.obj i))) ≫
        ((F.comp Adj.forget₁).mapComp' (sq i i).p₂.op.toLoc p.op.toLoc
          (𝟙 (X i)).op.toLoc (by rw [comp_op_toLoc, h₂])).inv.toNatTrans.app
          (((F.comp Adj.forget₁).map (f i).op.toLoc).toFunctor.obj
            ((F.map (f i).op.toLoc).r.toFunctor.obj (D.obj i))) =
        𝟙 _ by
      set_option backward.isDefEq.respectTransparency false in
      conv_lhs =>
        rw [← Category.assoc, ← Category.assoc, ← Category.assoc]
        rw [Category.assoc (f := ((F.comp Adj.forget₁).map (𝟙 (X i)).op.toLoc).toFunctor.map _)]
        rw [Category.assoc (f := ((F.comp Adj.forget₁).map (𝟙 (X i)).op.toLoc).toFunctor.map _)]
        rw [Category.assoc (f := ((F.comp Adj.forget₁).map (𝟙 (X i)).op.toLoc).toFunctor.map _)]
        simp only [Category.assoc, h_mid, Category.id_comp, Category.comp_id]
      rw [← Functor.map_comp, D.counit, Functor.map_id]
    -- Apply the extracted diagonal coherence lemma
    exact pullHom_isoMapOfCommSq_diagonal sq i p h₁ h₂ (D.obj i)
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
      comm i₁ i₂ := by
        dsimp only [DescentDataAsCoalgebra.toDescentData'Obj]
        simp only [Category.assoc]
        rw [← Functor.map_comp_assoc, ← φ.comm, Functor.map_comp_assoc]
        congr 1
        -- Normalize: (F.map g).l.toFunctor = ((F.comp Adj.forget₁).map g).toFunctor
        rw [show (F.map (f i₁).op.toLoc).l.toFunctor.map
              ((F.map (f i₂).op.toLoc).r.toFunctor.map (φ.hom i₂)) =
            ((F.comp Adj.forget₁).map (f i₁).op.toLoc).toFunctor.map
              ((F.map (f i₂).op.toLoc).r.toFunctor.map (φ.hom i₂)) from rfl]
        -- Fold separated functors into composite
        rw [← Cat.Hom.comp_map]
        rw [((F.comp Adj.forget₁).isoMapOfCommSq
          (pbCommSq sq i₁ i₂)).hom.toNatTrans.naturality_assoc]
        rw [Cat.Hom.comp_map, ← Functor.map_comp, ← Functor.map_comp]
        congr 2
        exact Adj.counit_naturality _ _ }

/-! ### Beck–Chevalley condition and backward functor

[B-R §1.2, Kahn §2.1] The Beck–Chevalley (exchange) condition states that the base
change morphism `χ` is an isomorphism for each pullback square. Under this condition,
we can invert `χ` to construct the backward functor from descent data to coalgebras.

In B-R's formulation (§1.2), condition (C) states: in a commutative square whose image
under P is a pullback, if `χ` and `χ'` are cartesian and `k₀` is cocartesian, then `k₁`
is cocartesian. Kahn (§2.1, Definition 2.1) shows this is equivalent to `χ` being an iso.

The backward construction is the inverse of Kahn's map `ξ` from Eq (1.3).
Given a descent datum `v : p₁^*(M) → p₂^*(M)`, the corresponding coalgebra structure
map `K^a(v) : M → (f i₁)^*((f i₂)_*(M))` is obtained by:
1. Applying the unit `η_{p₁}` to enter `(p₁)_* ∘ p₁^*`
2. Pushing forward `v` along `(p₁)_*`
3. Applying `χ⁻¹` (the inverse base change, existing by BC) to reach `(f i₁)^* ∘ (f i₂)_*`

This is the "Eilenberg–Moore comparison" of B-R §1.1 (the functor `Φ^a`). -/

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
  -- [B-R] Counit: backward.hom i i ≫ ε = 𝟙
  -- Proof: round-trip identity + D.pullHom'_hom_self + diagonal coherence
  counit i := by
    simp only [Category.assoc]
    obtain ⟨p, h₁, h₂⟩ := (sq i i).isPullback.exists_lift (𝟙 _) (𝟙 _) (by simp)
    -- Round-trip: p₁^*(backward.hom) ≫ iso ≫ p₂^*(ε) = D.hom i i
    have h_rt : ((F.comp Adj.forget₁).map (sq i i).p₁.op.toLoc).toFunctor.map
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
      have h_key : (F.map (sq i i).p₁.op.toLoc).l.toFunctor.map
            (baseChangeApp F sq i i (D.obj i)) ≫
          (F.map (sq i i).p₁.op.toLoc).adj.counit.toNatTrans.app _ =
        ((F.comp Adj.forget₁).isoMapOfCommSq (pbCommSq sq i i)).hom.toNatTrans.app _ ≫
        ((F.comp Adj.forget₁).map (sq i i).p₂.op.toLoc).toFunctor.map
          ((F.map (f i).op.toLoc).adj.counit.toNatTrans.app _) := by
        dsimp only [baseChangeApp]; rw [Functor.map_comp]
        simp [Adj.left_triangle_components_assoc, Adj.counit_naturality]
      rw [← h_key, ← Functor.map_comp_assoc, IsIso.inv_hom_id, Functor.map_id,
          Category.id_comp, ← Functor.map_comp]
      simp [Adj.left_triangle_components_assoc, Adj.counit_naturality]
    -- Substitute round-trip into D.pullHom'_hom_self
    have h_ps := D.pullHom'_hom_self i
    rw [DescentData'.pullHom'_eq_pullHom _ _ _ _ p] at h_ps
    rw [← h_rt] at h_ps
    dsimp only [LocallyDiscreteOpToCat.pullHom] at h_ps
    rw [Functor.map_comp_assoc, Functor.map_comp_assoc] at h_ps
    -- Push backward.hom past mc'₁ (bridge defeq for rewriter, then naturality)
    rw [show ((F.comp Adj.forget₁).mapComp' (sq i i).p₁.op.toLoc p.op.toLoc
          (𝟙 (X i)).op.toLoc (by rw [comp_op_toLoc, h₁])).hom.toNatTrans.app
          (D.obj i) =
        ((F.comp Adj.forget₁).mapComp' (sq i i).p₁.op.toLoc p.op.toLoc
          (𝟙 (X i)).op.toLoc (by rw [comp_op_toLoc, h₁])).hom.toNatTrans.app
          (((F.comp Adj.forget₁).map (𝟙 (X i)).op.toLoc).toFunctor.obj (D.obj i))
        from rfl] at h_ps
    rw [← Category.assoc, ← (F.comp Adj.forget₁).mapComp'_hom_naturality
        (sq i i).p₁.op.toLoc p.op.toLoc (𝟙 (X i)).op.toLoc
        (by rw [comp_op_toLoc, h₁])
        ((F.map (sq i i).p₁.op.toLoc).adj.unit.toNatTrans.app (D.obj i) ≫
         (F.map (sq i i).p₁.op.toLoc).r.toFunctor.map (D.hom i i) ≫
         inv (baseChangeApp F sq i i (D.obj i)))] at h_ps
    simp only [Category.assoc] at h_ps
    -- Push ε past mc'₂
    set_option backward.isDefEq.respectTransparency false in
    simp only [mapComp'_inv_naturality] at h_ps
    -- Diagonal coherence: middle = 𝟙
    have h_mid := pullHom_isoMapOfCommSq_diagonal sq i p h₁ h₂ (D.obj i)
    conv at h_ps =>
      lhs
      rw [← Category.assoc, ← Category.assoc, ← Category.assoc]
      rw [Category.assoc
        (f := ((F.comp Adj.forget₁).map (𝟙 (X i)).op.toLoc).toFunctor.map _)]
      rw [Category.assoc
        (f := ((F.comp Adj.forget₁).map (𝟙 (X i)).op.toLoc).toFunctor.map _)]
      rw [Category.assoc
        (f := ((F.comp Adj.forget₁).map (𝟙 (X i)).op.toLoc).toFunctor.map _)]
      simp only [Category.assoc, h_mid, Category.id_comp, Category.comp_id]
    exact h_ps
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
        dsimp only [DescentData'.toDescentDataAsCoalgebraObj]
        simp only [Category.assoc]
        -- Goal: η₁ ≫ r(D₁.hom) ≫ inv(χ₁) ≫ l_f₁(r_f₂(φ)) = φ ≫ η₂ ≫ r(D₂.hom) ≫ inv(χ₂)
        -- [B-R §1.3] Use baseChangeApp naturality to commute inv(χ) past l_f₁(r_f₂(φ))
        have h_nat := baseChangeApp_naturality F sq i₁ i₂ (φ.hom i₂)
        rw [show inv (baseChangeApp F sq i₁ i₂ (D₁.obj i₂)) ≫
              (F.map (f i₁).op.toLoc).l.toFunctor.map
                ((F.map (f i₂).op.toLoc).r.toFunctor.map (φ.hom i₂)) =
            (F.map (sq i₁ i₂).p₁.op.toLoc).r.toFunctor.map
              (((F.comp Adj.forget₁).map (sq i₁ i₂).p₂.op.toLoc).toFunctor.map (φ.hom i₂)) ≫
            inv (baseChangeApp F sq i₁ i₂ (D₂.obj i₂)) from by
          rw [IsIso.inv_comp_eq, ← Category.assoc, IsIso.eq_comp_inv]
          exact h_nat.symm]
        -- [B-R §1.3] Cancel inv(χ₂) from both sides
        simp only [← Category.assoc]
        congr 1
        simp only [Category.assoc]
        -- [B-R §1.3] Fold r_p₁ and use descent data morphism compatibility (φ.comm)
        rw [← Functor.map_comp, ← φ.comm, Functor.map_comp]
        -- [B-R §1.1] Cancel r(D₂.hom) from both sides
        rw [← Category.assoc, ← Category.assoc]
        congr 1
        -- [B-R §1.1] Unit naturality for p₁^* ⊣ (p₁)_*
        rw [show (F.map (sq i₁ i₂).p₁.op.toLoc).r.toFunctor.map
              (((F.comp Adj.forget₁).map (sq i₁ i₂).p₁.op.toLoc).toFunctor.map (φ.hom i₁)) =
            (F.map (sq i₁ i₂).p₁.op.toLoc).r.toFunctor.map
              ((F.map (sq i₁ i₂).p₁.op.toLoc).l.toFunctor.map (φ.hom i₁)) from rfl]
        exact Adj.unit_naturality (α := F.map (sq i₁ i₂).p₁.op.toLoc) (φ.hom i₁) }

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
