/-
Copyright (c) 2026 Richard Eager. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Richard Eager
-/
module

public import Mathlib.AlgebraicGeometry.Modules.PullbackTilde

/-!
# Pushforward and Tilde Compatibility for Affine Schemes

This file establishes Part (2) of [Stacks, Tag 01I9] (Lemma 26.7.3):

For affine schemes `Spec S`, `Spec R` and a ring homomorphism `f : R ⟶ S`
inducing `ψ = Spec.map f : Spec S ⟶ Spec R`:

**(2)** `ψ_* Ñ ≅ (N_R)~` functorially in the `S`-module `N`, i.e.,
  `tilde.functor S ⋙ pushforward (Spec.map f) ≅
    restrictScalars f ⋙ tilde.functor R`.

The natural map `(N_R)~ → ψ_* Ñ` is the adjunct (via `tilde_R ⊣ Γ_R`) of
  `N_R ≅ (Γ_S(Ñ))_R ≅ Γ_R(ψ_* Ñ)`
where the first step uses `IsIso tilde.adjunction.unit` and the second
uses `pushforwardΓRestrictScalarsIso`.

The key auxiliary result `mem_essImage_pushforward_tilde` shows `ψ_*(Ñ)`
lies in the essential image of `tilde_R` by proving the pushforward
sections on basic opens `D(r)` are localizations of `N_R` at `{r^n}`.
This bypasses the need for `SheafOfModules.Presentation` by using
`StructureSheaf.toOpen_comp_comap_apply` directly.

## Main results

- `Scheme.Modules.mem_essImage_tilde_of_basicOpen_localizations`:
  Affine criterion: a sheaf on `Spec R` is in `essImage(tilde_R)` if
  its restriction maps on basic opens are localizations of global sections.
- `Scheme.Modules.mem_essImage_pushforward_tilde`:
  `ψ_*(tilde_S(M)) ∈ essImage(tilde_R)`.
- `Scheme.Modules.pushforwardSpecTildeIso`:
  Part (2) of [Stacks 01I9].

## References

- [Stacks, Tag 01I9][stacks-project]

## Tags

algebraic geometry, quasi-coherent sheaves, base change, tilde,
pushforward
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Scheme.Modules
  TopologicalSpace

universe u

variable {R S : CommRingCat.{u}} (f : R ⟶ S)

/-! ### Lift between localizations is iso -/

/-- If `g` and `h` are both `S₀`-localizations of `A`, and
`α : B ⟶ C` satisfies `α.hom ∘ₗ g.hom = h.hom`, then `α` is an
isomorphism.
TODO: upstream to `Mathlib.Algebra.Module.LocalizedModule.Basic`. -/
lemma IsLocalizedModule.isIso_of_factoring {R₀ : Type u}
    [CommRing R₀] {A B C : ModuleCat.{u} R₀}
    (S₀ : Submonoid R₀) (g : A ⟶ B) (h : A ⟶ C)
    [IsLocalizedModule S₀ g.hom] [IsLocalizedModule S₀ h.hom]
    (α : B ⟶ C) (hfac : α.hom ∘ₗ g.hom = h.hom) :
    IsIso α := by
  have : α.hom =
      (IsLocalizedModule.linearEquiv S₀
        g.hom h.hom).toLinearMap := by
    have h1 := IsLocalizedModule.lift_unique S₀
      g.hom h.hom (IsLocalizedModule.map_units h.hom)
      α.hom hfac
    have h2 := IsLocalizedModule.lift_unique S₀
      g.hom h.hom (IsLocalizedModule.map_units h.hom)
      (IsLocalizedModule.linearEquiv S₀
        g.hom h.hom).toLinearMap
      (IsLocalizedModule.lift_comp S₀ g.hom h.hom
        (IsLocalizedModule.map_units h.hom))
    rw [← h1, h2]
  rw [show α = ModuleCat.ofHom
      (IsLocalizedModule.linearEquiv S₀
        g.hom h.hom).toLinearMap
    from ModuleCat.hom_ext this]
  exact (IsLocalizedModule.linearEquiv S₀
    g.hom h.hom).toModuleIso.isIso_hom

namespace AlgebraicGeometry.Scheme.Modules

/-! ### OrderTop instances for Opens -/

-- OrderTop for Opens is in CompleteLattice, but TC synthesis at
-- `.instances` transparency fails through the CommRingCat → Type
-- and Scheme → TopCat → Type coercion chains.
-- TODO: upstream to Mathlib.Topology.Opens or
-- Mathlib.AlgebraicGeometry.Scheme
instance orderTopOpensPrimeSpectrum {A : Type u} [CommRing A] :
    OrderTop (TopologicalSpace.Opens (PrimeSpectrum A)) :=
  (inferInstance : CompleteLattice _).toBoundedOrder.toOrderTop

instance orderTopOpensSpec {T : CommRingCat.{u}} :
    OrderTop ((Spec T).Opens) := orderTopOpensPrimeSpectrum

/-! ### Smul compatibility -/

section

variable (M : ModuleCat S)

lemma restrictScalars_pow_smul_eq {N : ModuleCat S}
    (r : R) (n : ℕ)
    (x : ((ModuleCat.restrictScalars f.hom).obj N)) :
    r ^ n • x = (f.hom r) ^ n • x := by
  have h : ∀ a : R, a • x = f.hom a • x :=
    fun a ↦ ModuleCat.restrictScalars.smul_def (R := ↑R) (f := f.hom) a x
  rw [h, map_pow]

/-! ### Localization compatibility -/

-- The R-linear tilde.toOpen is a localization at {r^n}
instance isLocalizedModule_restrictScalars_toOpen
    (r : R) :
    IsLocalizedModule (.powers r)
      ((ModuleCat.restrictScalars f.hom).map
        (tilde.toOpen M
          (PrimeSpectrum.basicOpen
            (f.hom r)))).hom := by
  rw [isLocalizedModule_iff]
  have hS := inferInstanceAs
    (IsLocalizedModule (.powers (f.hom r))
      (tilde.toOpen M
        (PrimeSpectrum.basicOpen (f.hom r))).hom)
  refine ⟨?_, ?_, ?_⟩
  · intro ⟨_, n, rfl⟩
    rw [Module.End.isUnit_iff]
    have := (Module.End.isUnit_iff _).mp
      (hS.map_units ⟨(f.hom r) ^ n, n, rfl⟩)
    convert this using 1
    ext x; exact restrictScalars_pow_smul_eq f r n x
  · intro y
    obtain ⟨⟨m, ⟨_, n, rfl⟩⟩, ht⟩ := hS.surj y
    refine ⟨⟨m, ⟨r ^ n, n, rfl⟩⟩, ?_⟩
    change r ^ n • y = _
    rw [restrictScalars_pow_smul_eq f r n y]
    exact ht
  · intro m₁ m₂ h
    obtain ⟨⟨_, n, rfl⟩, ht⟩ := hS.exists_of_eq h
    refine ⟨⟨r ^ n, n, rfl⟩, ?_⟩
    change r ^ n • m₁ = r ^ n • m₂
    rw [restrictScalars_pow_smul_eq f r n m₁,
      restrictScalars_pow_smul_eq f r n m₂]
    exact ht

/-! ### Pushforward restriction is a localization -/

/-- The restriction of the pushforward of `M~` to `D(r)` is a localization at `r`.
This factors through `inv(toOpen ⊤) ≫ toOpen(D(fr)) ≫ eqToHom`, requiring heavy defeq
reasoning. -/
theorem pushforward_res_isLocalizedModule (r : R) :
    IsLocalizedModule (.powers r)
      ((ModuleCat.restrictScalars f.hom).map
        ((modulesSpecToSheaf.obj
          ((tilde.functor S).obj M)).obj.map
          (homOfLE (le_top :
            (Opens.map (Spec.map f).base).obj
              (PrimeSpectrum.basicOpen r)
                ≤ ⊤)).op)).hom := by
  haveI : IsIso (tilde.toOpen M ⊤) :=
    tilde.isIso_toOpen_top
  haveI : IsIso
      ((ModuleCat.restrictScalars f.hom).map
        (tilde.toOpen M ⊤)) :=
    Functor.map_isIso _ _
  have heq := SpecMap_preimage_basicOpen f r
  have hfac :
      (ModuleCat.restrictScalars f.hom).map
        ((modulesSpecToSheaf.obj
          ((tilde.functor S).obj M)).obj.map
          (homOfLE (le_top :
            (Opens.map (Spec.map f).base).obj
              (PrimeSpectrum.basicOpen r)
                ≤ ⊤)).op) =
      inv ((ModuleCat.restrictScalars f.hom).map
        (tilde.toOpen M ⊤)) ≫
      ((ModuleCat.restrictScalars f.hom).map
        (tilde.toOpen M
          (PrimeSpectrum.basicOpen (f.hom r))) ≫
      (ModuleCat.restrictScalars f.hom).map
        ((modulesSpecToSheaf.obj
          ((tilde.functor S).obj M)).obj.map
          (eqToHom heq).op)) := by
    -- erw needed: dependent type mismatch in inv ≫ map prevents
    -- rw/simp from matching IsIso.eq_inv_comp or Functor.map_comp
    erw [IsIso.eq_inv_comp]
    erw [← Functor.map_comp]
  rw [hfac]
  haveI : IsLocalizedModule (.powers r)
      ((((ModuleCat.restrictScalars f.hom).map
          ((modulesSpecToSheaf.obj
            ((tilde.functor S).obj M)).obj.map
            (eqToHom heq).op)).hom) ∘ₗ
        (((ModuleCat.restrictScalars f.hom).map
          (tilde.toOpen M
            (PrimeSpectrum.basicOpen
              (f.hom r)))).hom)) :=
    IsLocalizedModule.of_linearEquiv (.powers r)
      (((ModuleCat.restrictScalars f.hom).map
        (tilde.toOpen M
          (PrimeSpectrum.basicOpen
            (f.hom r)))).hom)
      (asIso ((ModuleCat.restrictScalars f.hom).map
        ((modulesSpecToSheaf.obj
          ((tilde.functor S).obj M)).obj.map
          (eqToHom heq).op))).toLinearEquiv
  exact IsLocalizedModule.of_linearEquiv_right
    (.powers r)
    ((((ModuleCat.restrictScalars f.hom).map
        ((modulesSpecToSheaf.obj
          ((tilde.functor S).obj M)).obj.map
          (eqToHom heq).op)).hom) ∘ₗ
      (((ModuleCat.restrictScalars f.hom).map
        (tilde.toOpen M
          (PrimeSpectrum.basicOpen
            (f.hom r)))).hom))
    (asIso (inv
      ((ModuleCat.restrictScalars f.hom).map
        (tilde.toOpen M ⊤)))).toLinearEquiv

/-! ### Smul compatibility across universe levels -/

-- Both sides' R-actions factor through the native O_Y(ψ⁻¹(U))-module
-- via `StructureSheaf.toOpen_comp_comap_apply`.
lemma pushforward_smul_eq (U : (Spec R).Opens)
    (s : R)
    (x : ((modulesSpecToSheaf.obj
      ((pushforward (Spec.map f)).obj
        ((tilde.functor S).obj M))).obj.obj
        (Opposite.op U))) :
    s • x = @HSMul.hSMul R
      ((ModuleCat.restrictScalars f.hom).obj
        ((modulesSpecToSheaf.obj
          ((tilde.functor S).obj M)).obj.obj
          (Opposite.op
            ((Opens.map
              (Spec.map f).base).obj U))))
      _ instHSMul s x := by
  letI nativeMod := (((tilde.functor S).obj M).val.obj
      (Opposite.op ((Opens.map (Spec.map f).base).obj U))).isModule
  exact congrArg (fun r ↦ nativeMod.smul r (show _ from x))
    (StructureSheaf.toOpen_comp_comap_apply f.hom U s)

/-! ### Pushforward restriction at correct universe -/

/-- Variant of `pushforward_res_isLocalizedModule` at the correct universe level,
transferring the localization property from `restrictScalars` to `modulesSpecToSheaf`. -/
theorem pushforward_res_isLocalizedModule_direct
    (r : R) :
    let P := (pushforward (Spec.map f)).obj
      ((tilde.functor S).obj M)
    IsLocalizedModule (.powers r)
      ((modulesSpecToSheaf.obj P).obj.map
        (homOfLE (le_top :
          PrimeSpectrum.basicOpen r ≤ ⊤)).op).hom
      := by
  intro P
  rw [isLocalizedModule_iff]
  have hRS :=
    pushforward_res_isLocalizedModule f M r
  rw [isLocalizedModule_iff] at hRS
  obtain ⟨hmu, hsurj, hexists⟩ := hRS
  refine ⟨?_, ?_, ?_⟩
  · intro ⟨_, n, rfl⟩
    rw [Module.End.isUnit_iff]
    have := (Module.End.isUnit_iff _).mp
      (hmu ⟨r ^ n, n, rfl⟩)
    convert this using 1
    ext x
    exact pushforward_smul_eq f M
      (PrimeSpectrum.basicOpen r) (r ^ n) x
  · intro y
    obtain ⟨⟨m, s⟩, ht⟩ := hsurj y
    refine ⟨⟨m, s⟩, ?_⟩
    obtain ⟨_, n, rfl⟩ := s
    change r ^ n • y = _
    exact (pushforward_smul_eq f M
      (PrimeSpectrum.basicOpen r) (r ^ n) y).trans ht
  · intro m₁ m₂ h
    obtain ⟨⟨_, n, rfl⟩, ht⟩ := hexists h
    refine ⟨⟨r ^ n, n, rfl⟩, ?_⟩
    change r ^ n • m₁ = r ^ n • m₂
    exact (pushforward_smul_eq f M ⊤ (r ^ n) m₁).trans
      (ht.trans (pushforward_smul_eq f M ⊤ (r ^ n) m₂).symm)

/-! ### Affine criterion for essential image of tilde -/

/-- A sheaf of modules `P` on `Spec R` lies in the essential
image of `tilde.functor R` if the restriction map from global
sections to each basic open `D(r)` is a localization at the
submonoid `{rⁿ}`. This is the affine criterion for
quasi-coherence: it reduces the sheaf-theoretic question to an
algebra statement about localizations on a basis.

The proof shows `fromTildeΓ` is an isomorphism by cover-density
of basic opens: on each `D(r)`, the comparison map factors
through two localizations of `Γ(Spec R, P)` at `r`, hence is
an isomorphism by `IsLocalizedModule.isIso_of_factoring`. -/
lemma mem_essImage_tilde_of_basicOpen_localizations
    {R : CommRingCat.{u}} (P : (Spec R).Modules)
    (h : ∀ r : R,
      IsLocalizedModule (.powers r)
        ((modulesSpecToSheaf.obj P).obj.map
          (homOfLE (le_top :
            PrimeSpectrum.basicOpen r
              ≤ ⊤)).op).hom) :
    (tilde.functor R).essImage P := by
  rw [← isIso_fromTildeΓ_iff]
  let α := modulesSpecToSheaf.map P.fromTildeΓ
  let G := inducedFunctor
    (PrimeSpectrum.basicOpen (R := R))
  haveI hcd : G.IsCoverDense
      (_root_.Opens.grothendieckTopology
        (PrimeSpectrum R)) :=
    @TopCat.Opens.coverDense_inducedFunctor
      (TopCat.of (PrimeSpectrum R)) _
      _ PrimeSpectrum.isBasis_basic_opens
  suffices IsIso α from
    SpecModulesToSheafFullyFaithful (R := R)
      |>.isIso_of_isIso_map _
  apply @Functor.IsCoverDense.iso_of_restrict_iso
    _ _ _ _ _ _ _ G hcd inferInstance _ _ α
  haveI : ∀ (X : (InducedCategory
      (TopologicalSpace.Opens (PrimeSpectrum R))
      PrimeSpectrum.basicOpen)ᵒᵖ),
      IsIso ((G.op.whiskerLeft α.hom).app X) := by
    intro ⟨r'⟩
    let r : R := r'
    change IsIso (α.hom.app
      (Opposite.op (PrimeSpectrum.basicOpen r)))
    have tri := toOpen_fromTildeΓ_app P
      (PrimeSpectrum.basicOpen r)
    let g := tilde.toOpen
      ((modulesSpecToSheaf.obj P).presheaf.obj
        (Opposite.op ⊤))
      (PrimeSpectrum.basicOpen r)
    let hres := (modulesSpecToSheaf.obj P).obj.map
      (homOfLE (le_top :
        PrimeSpectrum.basicOpen r ≤ ⊤)).op
    exact @IsLocalizedModule.isIso_of_factoring
      _ _ _ _ _ (.powers r) g hres inferInstance (h r)
      (α.hom.app (Opposite.op (PrimeSpectrum.basicOpen r)))
      (LinearMap.ext fun x ↦ congrArg (fun φ ↦ φ.hom x) tri)
  exact NatIso.isIso_of_isIso_app _

/-! ### Essential image membership -/

/-- `f_*(tilde_S(M))` lies in the essential image of `tilde_R`.
This follows from `mem_essImage_tilde_of_basicOpen_localizations`
once we verify the localization hypothesis via
`pushforward_res_isLocalizedModule_direct`. -/
lemma mem_essImage_pushforward_tilde :
    (tilde.functor R).essImage
      ((pushforward (Spec.map f)).obj
        ((tilde.functor S).obj M)) :=
  mem_essImage_tilde_of_basicOpen_localizations _
    (pushforward_res_isLocalizedModule_direct f M)

end -- section variable (M : ModuleCat S)

/-! ### Natural transformation and iso -/

/-- The natural transformation `(N_R)~ ⟶ ψ_* Ñ` for Part (2) of
[Stacks 01I9]. Each component is the adjunct (via `tilde_R ⊣ Γ_R`)
of `N_R →[unit] (Γ_S(Ñ))_R →[iso⁻¹] Γ_R(ψ_* Ñ)`. -/
def pushforwardSpecTildeHom :
    ModuleCat.restrictScalars f.hom ⋙ tilde.functor R ⟶
    tilde.functor S ⋙ pushforward (Spec.map f) where
  app M :=
    ((tilde.adjunction (R := R)).homEquiv _ _).symm
      ((ModuleCat.restrictScalars f.hom).map
        ((tilde.adjunction (R := S)).unit.app M) ≫
      (pushforwardΓRestrictScalarsIso f).inv.app
        ((tilde.functor S).obj M))
  naturality M N g := by
    simp only [Functor.comp_obj, Functor.comp_map]
    -- erw needed: homEquiv_naturality_*_symm/unit.naturality/map_comp/inv.naturality
    -- through functor composition dependent types (upstream transparency gap)
    erw [← Adjunction.homEquiv_naturality_left_symm,
      ← Adjunction.homEquiv_naturality_right_symm]
    congr 1
    rw [← Category.assoc,
      ← (ModuleCat.restrictScalars f.hom).map_comp]
    erw [(tilde.adjunction (R := S)).unit.naturality g]
    simp only [Functor.comp_map]
    erw [(ModuleCat.restrictScalars f.hom).map_comp]
    rw [Category.assoc, Category.assoc]
    erw [(pushforwardΓRestrictScalarsIso f).inv.naturality
      ((tilde.functor S).map g)]
    rfl

/-- Each component of `pushforwardSpecTildeHom` is an isomorphism,
because it decomposes as `tilde.map(unit ≫ iso⁻¹) ≫ counit` where
each factor is iso. -/
lemma isIso_pushforwardSpecTildeHom_app (M : ModuleCat S) :
    IsIso ((pushforwardSpecTildeHom f).app M) := by
  haveI : IsIso ((tilde.adjunction (R := R)).counit.app
      ((pushforward (Spec.map f)).obj
        ((tilde.functor S).obj M))) :=
    isIso_fromTildeΓ_iff.mpr (mem_essImage_pushforward_tilde f M)
  haveI : IsIso ((ModuleCat.restrictScalars f.hom).map
      ((tilde.adjunction (R := S)).unit.app M)) :=
    Functor.map_isIso _ _
  haveI : IsIso ((pushforwardΓRestrictScalarsIso f).inv.app
      ((tilde.functor S).obj M)) := by
    haveI : IsIso (pushforwardΓRestrictScalarsIso f).inv := inferInstance
    exact inferInstance
  haveI : IsIso ((ModuleCat.restrictScalars f.hom).map
      ((tilde.adjunction (R := S)).unit.app M) ≫
    (pushforwardΓRestrictScalarsIso f).inv.app
      ((tilde.functor S).obj M)) :=
    @IsIso.comp_isIso _ _ _ _ _ _ _
      ‹IsIso ((ModuleCat.restrictScalars f.hom).map
        ((tilde.adjunction (R := S)).unit.app M))›
      ‹IsIso ((pushforwardΓRestrictScalarsIso f).inv.app
        ((tilde.functor S).obj M))›
  haveI : IsIso ((tilde.functor R).map
      ((ModuleCat.restrictScalars f.hom).map
        ((tilde.adjunction (R := S)).unit.app M) ≫
      (pushforwardΓRestrictScalarsIso f).inv.app
        ((tilde.functor S).obj M))) :=
    Functor.map_isIso _ _
  simp only [pushforwardSpecTildeHom, Functor.comp_obj]
  -- erw needed: homEquiv_counit through universe coercion
  erw [Adjunction.homEquiv_counit]
  exact @IsIso.comp_isIso _ _ _ _ _ _ _
    ‹IsIso ((tilde.functor R).map
      ((ModuleCat.restrictScalars f.hom).map
        ((tilde.adjunction (R := S)).unit.app M) ≫
      (pushforwardΓRestrictScalarsIso f).inv.app
        ((tilde.functor S).obj M)))›
    ‹IsIso ((tilde.adjunction (R := R)).counit.app
      ((pushforward (Spec.map f)).obj
        ((tilde.functor S).obj M)))›

/-- Part (2) of [Stacks 01I9] (Lemma 26.7.3). For a ring
homomorphism `f : R ⟶ S`, pushing forward along `Spec.map f`
intertwines with restriction of scalars through the tilde
functor. -/
@[stacks 01I9]
def pushforwardSpecTildeIso :
    ModuleCat.restrictScalars f.hom ⋙ tilde.functor R ≅
    tilde.functor S ⋙ pushforward (Spec.map f) :=
  haveI := fun M ↦ isIso_pushforwardSpecTildeHom_app f M
  NatIso.ofComponents
    (fun M ↦ asIso ((pushforwardSpecTildeHom f).app M))
    (fun g ↦ (pushforwardSpecTildeHom f).naturality g)

end AlgebraicGeometry.Scheme.Modules
