/-
Copyright (c) 2026 Richard Eager. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Richard Eager
-/
module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings

/-!
# Pullback and Tilde Compatibility for Affine Schemes

This file establishes Part (1) of [Stacks, Tag 01I9] (Lemma 26.7.3):

For affine schemes `Spec S`, `Spec R` and a ring homomorphism `f : R ⟶ S` inducing
`ψ = Spec.map f : Spec S ⟶ Spec R`:

**(1)** `ψ* M̃ ≅ (S ⊗_R M)~` functorially in the `R`-module `M`, i.e.,
  `tilde.functor R ⋙ pullback (Spec.map f) ≅ extendScalars f ⋙ tilde.functor S`.

The proof shows that both sides are left adjoints of naturally isomorphic right adjoints
and applies `Adjunction.leftAdjointUniq`. The key auxiliary result
`pushforwardΓRestrictScalarsIso` identifies the two right adjoints:

- LHS right adjoint: `pushforward (Spec.map f) ⋙ moduleSpecΓFunctor`
- RHS right adjoint: `moduleSpecΓFunctor ⋙ restrictScalars f`

## Main results

- `Scheme.Modules.pushforwardΓRestrictScalarsIso`: For `Spec.map f`, the pushforward
  followed by global sections on the base is naturally isomorphic to global sections
  on the source followed by restriction of scalars.
- `Scheme.Modules.pullbackSpecTildeIso`: Part (1) of [Stacks 01I9]. Pullback along
  `Spec.map f` commutes with the tilde functor up to extension of scalars.

## References

- [Stacks, Tag 01I9](https://stacks.math.columbia.edu/tag/01I9)

## Tags

algebraic geometry, quasi-coherent sheaves, base change, tilde, pullback
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Scheme.Modules

universe u

variable {R S : CommRingCat.{u}} (f : R ⟶ S)

namespace AlgebraicGeometry.Scheme.Modules

/-- For `Spec.map f : Spec S ⟶ Spec R`, the pushforward followed by taking global
sections on the base is naturally isomorphic to taking global sections on the source
followed by restriction of scalars along `f`.
This is the key auxiliary for `pullbackSpecTildeIso`. -/
def pushforwardΓRestrictScalarsIso :
    pushforward (Spec.map f) ⋙ (moduleSpecΓFunctor : (Spec R).Modules ⥤ _) ≅
    (moduleSpecΓFunctor : (Spec S).Modules ⥤ _) ⋙ ModuleCat.restrictScalars f.hom :=
  NatIso.ofComponents (fun M ↦
    letI inst₁ := ((pushforward (Spec.map f) ⋙ moduleSpecΓFunctor).obj M).isModule
    letI inst₂ :=
      ((moduleSpecΓFunctor ⋙ ModuleCat.restrictScalars f.hom).obj M).isModule
    LinearEquiv.toModuleIso (R := ↑R) (m₁ := inst₁) (m₂ := inst₂)
    (X₁ := (pushforward (Spec.map f) ⋙ moduleSpecΓFunctor).obj M)
    (X₂ := (moduleSpecΓFunctor ⋙ ModuleCat.restrictScalars f.hom).obj M)
    { __ := AddEquiv.refl _
      map_smul' := fun r x => by
        dsimp
        erw [ModuleCat.restrictScalars.smul_def,
          ModuleCat.restrictScalars.smul_def,
          ModuleCat.restrictScalars.smul_def,
          ModuleCat.restrictScalars.smul_def]
        congr 1
        exact congrArg (fun k : R ⟶ Scheme.Γ.obj (Opposite.op (Spec S)) =>
          k.hom r) (Scheme.ΓSpecIso_inv_naturality f).symm })
    (fun g => by ext; rfl)

/-- Part (1) of [Stacks 01I9] (Lemma 26.7.3). For a ring homomorphism `f : R ⟶ S`,
pulling back along `Spec.map f` intertwines with extension of scalars through the
tilde functor. Both sides are left adjoints of naturally isomorphic right adjoints
(`pushforwardΓRestrictScalarsIso`), so the result follows from
`Adjunction.leftAdjointUniq`. -/
@[stacks 01I9]
def pullbackSpecTildeIso :
    tilde.functor R ⋙ pullback (Spec.map f) ≅
    ModuleCat.extendScalars f.hom ⋙ tilde.functor S :=
  (tilde.adjunction (R := R) |>.comp
    (pullbackPushforwardAdjunction (Spec.map f))).leftAdjointUniq
    ((ModuleCat.extendRestrictScalarsAdj f.hom |>.comp
      (tilde.adjunction (R := S))).ofNatIsoRight
      (pushforwardΓRestrictScalarsIso f).symm)

end AlgebraicGeometry.Scheme.Modules
