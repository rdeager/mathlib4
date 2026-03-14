/-
Copyright (c) 2026 Richard Eager. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Richard Eager
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Localization
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

namespace AlgebraicGeometry.Scheme.Modules

/-! ### OrderTop instances for Opens -/

-- TC synthesis fails to find `OrderTop` through the `CommRingCat → Type` coercion chain.
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

/-- The restriction of the pushforward of `M~` to `D(r)` is a localization at `r`. -/
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
    exact (IsIso.eq_inv_comp (α := (ModuleCat.restrictScalars f.hom).map
      (tilde.toOpen M ⊤))).mpr
      ((ModuleCat.restrictScalars f.hom).map_comp _ _).symm
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

/-- A sheaf of modules `P` on `Spec R` lies in the essential image of `tilde.functor R` if
the restriction map from global sections to each basic open `D(r)` is a localization at `{rⁿ}`.
The proof uses cover-density of basic opens and `IsLocalizedModule.isIso_of_factoring`. -/
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

/-- `f_*(tilde_S(M))` lies in the essential image of `tilde_R`. -/
lemma mem_essImage_pushforward_tilde :
    (tilde.functor R).essImage
      ((pushforward (Spec.map f)).obj
        ((tilde.functor S).obj M)) :=
  mem_essImage_tilde_of_basicOpen_localizations _
    (pushforward_res_isLocalizedModule_direct f M)

end -- section variable (M : ModuleCat S)

/-! ### Natural transformation and iso -/

/-- Inner diagram chase for `pushforwardSpecTildeHom` naturality, extracted from the `where`
clause to avoid elaboration rigidity with `rw` on `NatTrans.naturality`. -/
private lemma pushforwardSpecTildeHom_naturality_aux
    (M N : ModuleCat S) (g : M ⟶ N) :
    (ModuleCat.restrictScalars f.hom).map g ≫
      (ModuleCat.restrictScalars f.hom).map
        ((tilde.adjunction (R := S)).unit.app N) ≫
        (pushforwardΓRestrictScalarsIso f).inv.app
          ((tilde.functor S).obj N) =
    ((ModuleCat.restrictScalars f.hom).map
        ((tilde.adjunction (R := S)).unit.app M) ≫
      (pushforwardΓRestrictScalarsIso f).inv.app
        ((tilde.functor S).obj M)) ≫
      moduleSpecΓFunctor.map
        ((pushforward (Spec.map f)).map
          ((tilde.functor S).map g)) := by
  have h_unit : g ≫ (tilde.adjunction (R := S)).unit.app N =
      (tilde.adjunction (R := S)).unit.app M ≫
        moduleSpecΓFunctor.map ((tilde.functor S).map g) := by
    simpa only [Functor.id_map, Functor.comp_map] using
      (tilde.adjunction (R := S)).unit.naturality g
  have h_inv : (ModuleCat.restrictScalars f.hom).map
        (moduleSpecΓFunctor.map ((tilde.functor S).map g)) ≫
      (pushforwardΓRestrictScalarsIso f).inv.app
        ((tilde.functor S).obj N) =
    (pushforwardΓRestrictScalarsIso f).inv.app
        ((tilde.functor S).obj M) ≫
      moduleSpecΓFunctor.map
        ((pushforward (Spec.map f)).map
          ((tilde.functor S).map g)) := by
    simpa only [Functor.comp_map] using
      (pushforwardΓRestrictScalarsIso f).inv.naturality
        ((tilde.functor S).map g)
  rw [← Category.assoc,
    ← (ModuleCat.restrictScalars f.hom).map_comp, h_unit]
  exact (congrArg (· ≫ _)
    ((ModuleCat.restrictScalars f.hom).map_comp _ _)).trans
    ((Category.assoc _ _ _).trans
      ((congrArg (_ ≫ ·) h_inv).trans
        (Category.assoc _ _ _).symm))

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
    change (tilde.functor R).map _ ≫ (Adjunction.homEquiv _ _ _).symm _ =
      (Adjunction.homEquiv _ _ _).symm _ ≫ _
    rw [← Adjunction.homEquiv_naturality_left_symm,
      ← Adjunction.homEquiv_naturality_right_symm]
    congr 1
    exact pushforwardSpecTildeHom_naturality_aux f M N g

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
      ((tilde.adjunction (R := S)).unit.app M)) := Functor.map_isIso _ _
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
        ((tilde.functor S).obj M))) := Functor.map_isIso _ _
  simp only [pushforwardSpecTildeHom, Functor.comp_obj]
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
