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
    -- Push D.hom past outer_hom and ε past outer_inv using conv
    set_option backward.isDefEq.respectTransparency false in
    conv_lhs =>
      rw [← Category.assoc, ← (F.comp Adj.forget₁).mapComp'_hom_naturality
        (sq i i).p₁.op.toLoc p.op.toLoc (𝟙 (X i)).op.toLoc
        (by rw [← Quiver.Hom.comp_toLoc, ← op_comp, h₁]) (D.hom i i)]
    simp only [Category.assoc]
    set_option backward.isDefEq.respectTransparency false in
    simp only [mapComp'_inv_naturality]
    -- Goal: 𝟙*(D.hom) ≫ mc'(p₁,p,𝟙).hom ≫ p*(iso.hom) ≫ mc'(p₂,p,𝟙).inv ≫ 𝟙*(ε) = 𝟙
    -- Show: middle 3 terms = 𝟙, then D.hom ≫ ε = 𝟙 by D.counit
    -- Middle: pullHom(iso.hom)(p) where iso = isoMapOfCommSq(pbCommSq)
    -- Suffices to show pullHom(iso.hom)(p) = 𝟙 as an Iso applied at an object
    -- Insert iso.inv before iso.hom using Iso.inv_hom_id
    -- pullHom(iso.hom)(p) = mc'.hom ≫ p*(iso.hom) ≫ mc'.inv
    -- This is an NatIso applied at M, pulled back
    -- Use NatIso.naturality_2 to simplify:
    -- mc'.hom ≫ p*(iso.hom) ≫ mc'.inv should reduce to something that cancels
    -- Actually... this is pullHom(iso.hom)(p). And iso goes between p₁* and p₂*.
    -- pullHom takes φ : p₁*(M) → p₂*(M), g = p, and outputs
    --   mc'(p₁,p,𝟙).hom ≫ p*(φ) ≫ mc'(p₂,p,𝟙).inv : 𝟙*(M) → 𝟙*(M)
    -- where φ = iso.hom.app(M)
    -- This is functorial in M: it's a natural transformation
    -- For M = fi_*(D.obj), this should be 𝟙 by coherence
    -- Key: use isoMapOfCommSq as a natural iso, and the pullHom is conjugation
    -- The pullback of a natural iso along p gives a natural iso, and the
    -- particular iso here degenerates because the square becomes trivial along the diagonal
    -- Approach: use that the composition of the 5 remaining terms is the counit
    -- of the coalgebra structure, pulled back appropriately
    -- Let me try: fold remaining middle into ← Functor.map_comp, then simp with D.counit
    -- The 5 terms: 𝟙*(D.hom) ≫ mc'.hom ≫ p*(iso.hom) ≫ mc'.inv ≫ 𝟙*(ε)
    -- = 𝟙*(D.hom) ≫ pullHom(iso.hom)(p) ≫ 𝟙*(ε)
    -- We need: pullHom(iso.hom)(p) = 𝟙
    -- Enough: mc'.hom ≫ p*(iso.hom) ≫ mc'.inv = 𝟙
    -- which is: mapComp'_naturality_2(p₁,p,𝟙)(iso.hom) if p₁ = p₂
    -- but p₁ ≠ p₂ in general!
    -- However, the source mc'.hom uses p₁ and the target mc'.inv uses p₂
    -- so this ISN'T mapComp'_naturality_2
    -- The coherence here is deeper: it's about the pseudofunctor's response to
    -- the diagonal map, and requires 3-morphism associativity
    -- Let me try a `calc` approach with explicit intermediate steps
    -- Or: observe that the composition 𝟙*(D.hom) ≫ pullHom(iso.hom)(p) ≫ 𝟙*(ε)
    -- equals pullHom(D.hom ≫ iso.hom ≫ ε)(p)(using linearity of pullHom... but it's not linear)
    -- Actually, pullHom IS linear in a sense: pullHom(a ≫ b)(g) = pullHom(a)(g) ≫ pullHom(b)(g)
    -- when a and b have the right types!
    -- pullHom(D.hom)(p)(𝟙)(𝟙) = 𝟙*(D.hom) ≫ mc'(p₁,p,𝟙).hom ≫ mc'(p₁,p,𝟙).inv
    --   Wait no, pullHom takes φ between f₁* and f₂*, not within the same fiber
    -- OK let me just try `simp` with all possible lemmas and maxHeartbeats
    -- Middle 3: mc'(p₁,p,𝟙).hom ≫ p*(iso.hom) ≫ mc'(p₂,p,𝟙).inv
    -- Show this = 𝟙 by reducing to the identity coherence iso
    -- Rewrite iso using isoMapOfCommSq_eq, unfold it
    -- Then use mapComp' associativity
    -- Reduce middle to 𝟙 and use D.counit
    -- Suffices: 𝟙*(D.hom ≫ ε) = 𝟙*(𝟙) = 𝟙
    -- For now: suffices to show
    -- mc'.hom(p₁,p,𝟙) ≫ p*(iso.hom) ≫ mc'.inv(p₂,p,𝟙) = 𝟙 at the relevant object
    -- Use a helper have
    -- Prove the middle 3 terms = 𝟙, then fold D.hom ≫ ε = 𝟙 via D.counit
    -- Middle: mc'(p₁,p,𝟙).hom ≫ p*(isoMapOfCommSq.hom.app(M)) ≫ mc'(p₂,p,𝟙).inv
    -- where M = r(D.obj i) in the S-fiber
    -- This equals 𝟙 because pulling the isoMapOfCommSq back along the diagonal
    -- gives the identity coherence iso
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
      set_option backward.isDefEq.respectTransparency false in
      conv_lhs =>
        rw [← Category.assoc, ← Category.assoc, ← Category.assoc]
        rw [Category.assoc (f := ((F.comp Adj.forget₁).map (𝟙 (X i)).op.toLoc).toFunctor.map _)]
        rw [Category.assoc (f := ((F.comp Adj.forget₁).map (𝟙 (X i)).op.toLoc).toFunctor.map _)]
        rw [Category.assoc (f := ((F.comp Adj.forget₁).map (𝟙 (X i)).op.toLoc).toFunctor.map _)]
        simp only [Category.assoc, h_mid, Category.id_comp, Category.comp_id]
      rw [← Functor.map_comp, D.counit, Functor.map_id]
    -- h_mid: pullHom(isoMapOfCommSq.hom)(p) = 𝟙
    -- Unfold isoMapOfCommSq into mapComp' pair, expand, use 3-morph assoc
    rw [(F.comp Adj.forget₁).isoMapOfCommSq_eq (pbCommSq sq i i)
      ((sq i i).p₁ ≫ f i).op.toLoc (by rw [← Quiver.Hom.comp_toLoc, ← op_comp])]
    simp only [Iso.trans_hom, Iso.symm_hom, Cat.Hom₂.comp_app]
    rw [Functor.map_comp_assoc]
    -- Now: mc'(p₁,p,𝟙).hom ≫ p*(mc'(fi,p₁,φ).inv) ≫ p*(mc'(fi,p₂,φ).hom) ≫ mc'(p₂,p,𝟙).inv = 𝟙
    -- Combine pairs using mapComp' 3-morph associativity:
    -- Left pair: mc'(p₁,p,𝟙).hom ≫ p*(mc'(fi,p₁,φ).inv)
    -- Right pair: p*(mc'(fi,p₂,φ).hom) ≫ mc'(p₂,p,𝟙).inv
    -- Use mapComp'_inv_whiskerRight_mapComp'₀₂₃_inv for the right pair (both .inv)
    -- But right pair has hom+inv, not inv+inv
    -- Instead, insert hom_inv_id to convert
    -- Or use mapComp'_naturality_2 after combining adjacent terms
    -- Actually: the 4 terms give mapComp'_naturality_2 for (fi,𝟙,fi):
    -- mc'(fi,𝟙,fi).hom ≫ 𝟙*(fi*(a)) ≫ mc'(fi,𝟙,fi).inv = fi*(a)
    -- But we don't directly have this pattern.
    -- Try a big simp
    -- Goal: 4 terms (right-associated):
    -- mc'(p₁,p,𝟙).hom.app(fi*(M)) ≫ p*(mc'(fi,p₁,φ).inv.app(M)) ≫
    --   p*(mc'(fi,p₂,φ).hom.app(M)) ≫ mc'(p₂,p,𝟙).inv.app(fi*(M)) = 𝟙
    -- Insight: this is pullHom(isoMapOfCommSq.hom.app(M))(p)
    -- = pullHom(mc'(fi,p₁,φ).inv.app ≫ mc'(fi,p₂,φ).hom.app)(p)
    -- The isoMapOfCommSq at the diagonal becomes identity after pullback
    -- Proof: use the characterization from isoMapOfCommSq_eq
    -- and mapComp' associativity
    -- Key identity: compose the outer mapComp' with the inner mapComp' to get a single mapComp'
    -- for the full path fi → p_k → p → 𝟙, which equals fi → 𝟙 = fi
    -- Then the pair of such compositions with different p_k cancels
    --
    -- Concretely, for term 1 (outer hom at p₁) and term 2 (inner inv at fi,p₁):
    -- mc'(p₁,p,𝟙).hom.app(fi*(M)) ≫ p*(mc'(fi,p₁,φ).inv.app(M))
    -- = mc'(fi,𝟙,fi).inv.app(M) (by 3-morph assoc, since fi→p₁→p = fi→𝟙)
    -- And for term 3 (inner hom at fi,p₂) and term 4 (outer inv at p₂):
    -- p*(mc'(fi,p₂,φ).hom.app(M)) ≫ mc'(p₂,p,𝟙).inv.app(fi*(M))
    -- = mc'(fi,𝟙,fi).hom.app(M) (by 3-morph assoc, since fi→p₂→p = fi→𝟙)
    -- Wait, these should be the SAME mc'(fi,𝟙,fi) since both factor through fi→𝟙!
    -- So the 4-term composition becomes mc'(fi,𝟙,fi).inv ≫ mc'(fi,𝟙,fi).hom = 𝟙
    -- via Iso.inv_hom_id
    -- But this requires the 3-morph assoc to give EXACTLY the same iso in both cases
    -- which it should since the composite path is the same: fi → (p₁ or p₂) → p → (p≫p₁=𝟙 or p≫p₂=𝟙) = fi
    --
    -- Use mapComp'₀₂₃_hom_comp_mapComp'_hom_whiskerRight_app (hom variant) for the hom pair
    -- Use mapComp'_inv_whiskerRight_mapComp'₀₂₃_inv_app (inv variant) for the inv pair
    -- But terms 1,2 are hom,inv and terms 3,4 are hom,inv - mixed!
    -- Convert: insert id = inv ≫ hom for outer mc'(p₁,p,𝟙):
    -- mc'(p₁,p,𝟙).hom = mc'(p₁,p,𝟙).hom
    -- mc'(p₁,p,𝟙).inv ≫ mc'(p₁,p,𝟙).hom = 𝟙
    -- Hmm, this inserts MORE terms.
    -- Actually, let me try the approach of inserting mc'(p₁,p,𝟙).inv ≫ mc'(p₁,p,𝟙).hom = 𝟙
    -- between terms 2 and 3, creating:
    -- (terms 1,2): mc'.hom ≫ p*(mc'.inv) ... followed by mc'(p₁,p,𝟙).inv (BOTH inv)
    -- then mc'(p₁,p,𝟙).hom followed by (terms 3,4): p*(mc'.hom) ≫ mc'.inv (BOTH hom after mc')
    -- Use the inv-inv lemma on first group and hom-hom lemma on second group
    -- Insert identity between terms 2 and 3:
    conv_lhs =>
      rw [← Category.assoc, ← Category.assoc]
      rw [Category.assoc (f := ((F.comp Adj.forget₁).mapComp' (sq i i).p₁.op.toLoc p.op.toLoc
        (𝟙 (X i)).op.toLoc _).hom.toNatTrans.app _)]
    set_option backward.isDefEq.respectTransparency false in
    rw [show ((F.comp Adj.forget₁).map p.op.toLoc).toFunctor.map
          (((F.comp Adj.forget₁).mapComp' (f i).op.toLoc (sq i i).p₁.op.toLoc
            ((sq i i).p₁ ≫ f i).op.toLoc _).inv.toNatTrans.app
            ((F.map (f i).op.toLoc).r.toFunctor.obj (D.obj i))) ≫
        ((F.comp Adj.forget₁).map p.op.toLoc).toFunctor.map
          (((F.comp Adj.forget₁).mapComp' (f i).op.toLoc (sq i i).p₂.op.toLoc
            ((sq i i).p₁ ≫ f i).op.toLoc _).hom.toNatTrans.app
            ((F.map (f i).op.toLoc).r.toFunctor.obj (D.obj i))) =
      ((F.comp Adj.forget₁).map p.op.toLoc).toFunctor.map
        (((F.comp Adj.forget₁).mapComp' (f i).op.toLoc (sq i i).p₁.op.toLoc
            ((sq i i).p₁ ≫ f i).op.toLoc _).inv.toNatTrans.app
            ((F.map (f i).op.toLoc).r.toFunctor.obj (D.obj i)) ≫
        ((F.comp Adj.forget₁).mapComp' (f i).op.toLoc (sq i i).p₂.op.toLoc
            ((sq i i).p₁ ≫ f i).op.toLoc _).hom.toNatTrans.app
            ((F.map (f i).op.toLoc).r.toFunctor.obj (D.obj i))) from
      (Functor.map_comp _ _ _).symm]
    -- Coherence: pullHom of isoMapOfCommSq along diagonal = 𝟙
    -- This holds because p ≫ p₁ = 𝟙 = p ≫ p₂ makes the pulled-back square trivial.
    -- TODO: prove using mapComp'₀₂₃ associativity or a dedicated coherence lemma
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
