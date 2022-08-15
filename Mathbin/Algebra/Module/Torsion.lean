/-
Copyright (c) 2022 Pierre-Alexandre Bazin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre-Alexandre Bazin
-/
import Mathbin.Algebra.DirectSum.Module
import Mathbin.LinearAlgebra.Isomorphisms
import Mathbin.GroupTheory.Torsion
import Mathbin.RingTheory.Coprime.Ideal
import Mathbin.RingTheory.Finiteness

/-!
# Torsion submodules

## Main definitions

* `torsion_of R M x` : the torsion ideal of `x`, containing all `a` such that `a • x = 0`.
* `submodule.torsion_by R M a` : the `a`-torsion submodule, containing all elements `x` of `M` such
  that `a • x = 0`.
* `submodule.torsion_by_set R M s` : the submodule containing all elements `x` of `M` such that
  `a • x = 0` for all `a` in `s`.
* `submodule.torsion' R M S` : the `S`-torsion submodule, containing all elements `x` of `M` such
  that `a • x = 0` for some `a` in `S`.
* `submodule.torsion R M` : the torsion submoule, containing all elements `x` of `M` such that
  `a • x = 0` for some non-zero-divisor `a` in `R`.
* `module.is_torsion_by R M a` : the property that defines a `a`-torsion module. Similarly,
  `is_torsion_by_set`, `is_torsion'` and `is_torsion`.
* `module.is_torsion_by_set.module` : Creates a `R ⧸ I`-module from a `R`-module that
  `is_torsion_by_set R _ I`.

## Main statements

* `quot_torsion_of_equiv_span_singleton` : isomorphism between the span of an element of `M` and
  the quotient by its torsion ideal.
* `torsion' R M S` and `torsion R M` are submodules.
* `torsion_by_set_eq_torsion_by_span` : torsion by a set is torsion by the ideal generated by it.
* `submodule.torsion_by_is_torsion_by` : the `a`-torsion submodule is a `a`-torsion module.
  Similar lemmas for `torsion'` and `torsion`.
* `submodule.torsion_by_is_internal` : a `∏ i, p i`-torsion module is the internal direct sum of its
  `p i`-torsion submodules when the `p i` are pairwise coprime. A more general version with coprime
  ideals is `submodule.torsion_by_set_is_internal`.
* `submodule.no_zero_smul_divisors_iff_torsion_bot` : a module over a domain has
  `no_zero_smul_divisors` (that is, there is no non-zero `a`, `x` such that `a • x = 0`)
  iff its torsion submodule is trivial.
* `submodule.quotient_torsion.torsion_eq_bot` : quotienting by the torsion submodule makes the
  torsion submodule of the new module trivial. If `R` is a domain, we can derive an instance
  `submodule.quotient_torsion.no_zero_smul_divisors : no_zero_smul_divisors R (M ⧸ torsion R M)`.

## Notation

* The notions are defined for a `comm_semiring R` and a `module R M`. Some additional hypotheses on
  `R` and `M` are required by some lemmas.
* The letters `a`, `b`, ... are used for scalars (in `R`), while `x`, `y`, ... are used for vectors
  (in `M`).

## Tags

Torsion, submodule, module, quotient
-/


namespace Ideal

section TorsionOf

variable (R M : Type _) [Semiringₓ R] [AddCommMonoidₓ M] [Module R M]

/-- The torsion ideal of `x`, containing all `a` such that `a • x = 0`.-/
@[simps]
def torsionOf (x : M) : Ideal R :=
  (LinearMap.toSpanSingleton R M x).ker

@[simp]
theorem torsion_of_zero : torsionOf R M (0 : M) = ⊤ := by
  simp [← torsion_of]

variable {R M}

@[simp]
theorem mem_torsion_of_iff (x : M) (a : R) : a ∈ torsionOf R M x ↔ a • x = 0 :=
  Iff.rfl

variable (R)

@[simp]
theorem torsion_of_eq_top_iff (m : M) : torsionOf R M m = ⊤ ↔ m = 0 := by
  refine'
    ⟨fun h => _, fun h => by
      simp [← h]⟩
  rw [← one_smul R m, ← mem_torsion_of_iff m (1 : R), h]
  exact Submodule.mem_top

@[simp]
theorem torsion_of_eq_bot_iff_of_no_zero_smul_divisors [Nontrivial R] [NoZeroSmulDivisors R M] (m : M) :
    torsionOf R M m = ⊥ ↔ m ≠ 0 := by
  refine' ⟨fun h contra => _, fun h => (Submodule.eq_bot_iff _).mpr fun r hr => _⟩
  · rw [contra, torsion_of_zero] at h
    exact bot_ne_top.symm h
    
  · rw [mem_torsion_of_iff, smul_eq_zero] at hr
    tauto
    

/-- See also `complete_lattice.independent.linear_independent` which provides the same conclusion
but requires the stronger hypothesis `no_zero_smul_divisors R M`. -/
theorem CompleteLattice.Independent.linear_independent' {ι R M : Type _} {v : ι → M} [Ringₓ R] [AddCommGroupₓ M]
    [Module R M] (hv : CompleteLattice.Independent fun i => R∙v i) (h_ne_zero : ∀ i, Ideal.torsionOf R M (v i) = ⊥) :
    LinearIndependent R v := by
  refine' linear_independent_iff_not_smul_mem_span.mpr fun i r hi => _
  replace hv := complete_lattice.independent_def.mp hv i
  simp only [← supr_subtype', Submodule.span_range_eq_supr, ← disjoint_iff] at hv
  have : r • v i ∈ ⊥ := by
    rw [← hv, Submodule.mem_inf]
    refine' ⟨submodule.mem_span_singleton.mpr ⟨r, rfl⟩, _⟩
    convert hi
    ext
    simp
  rw [← Submodule.mem_bot R, ← h_ne_zero i]
  simpa using this

end TorsionOf

section

variable (R M : Type _) [Ringₓ R] [AddCommGroupₓ M] [Module R M]

/-- The span of `x` in `M` is isomorphic to `R` quotiented by the torsion ideal of `x`.-/
noncomputable def quotTorsionOfEquivSpanSingleton (x : M) : (R ⧸ torsionOf R M x) ≃ₗ[R] R∙x :=
  (LinearMap.toSpanSingleton R M x).quotKerEquivRange.trans <|
    LinearEquiv.ofEq _ _ (LinearMap.span_singleton_eq_range R M x).symm

variable {R M}

@[simp]
theorem quot_torsion_of_equiv_span_singleton_apply_mk (x : M) (a : R) :
    quotTorsionOfEquivSpanSingleton R M x (Submodule.Quotient.mk a) = a • ⟨x, Submodule.mem_span_singleton_self x⟩ :=
  rfl

end

end Ideal

open nonZeroDivisors

section Defs

variable (R M : Type _) [CommSemiringₓ R] [AddCommMonoidₓ M] [Module R M]

namespace Submodule

/-- The `a`-torsion submodule for `a` in `R`, containing all elements `x` of `M` such that
  `a • x = 0`. -/
@[simps]
def torsionBy (a : R) : Submodule R M :=
  (DistribMulAction.toLinearMap _ _ a).ker

/-- The submodule containing all elements `x` of `M` such that `a • x = 0` for all `a` in `s`. -/
@[simps]
def torsionBySet (s : Set R) : Submodule R M :=
  inf (torsionBy R M '' s)

/-- The `S`-torsion submodule, containing all elements `x` of `M` such that `a • x = 0` for some
`a` in `S`. -/
@[simps]
def torsion' (S : Type _) [CommMonoidₓ S] [DistribMulAction S M] [SmulCommClass S R M] : Submodule R M where
  Carrier := { x | ∃ a : S, a • x = 0 }
  zero_mem' := ⟨1, smul_zero _⟩
  add_mem' := fun x y ⟨a, hx⟩ ⟨b, hy⟩ =>
    ⟨b * a, by
      rw [smul_add, mul_smul, mul_comm, mul_smul, hx, hy, smul_zero, smul_zero, add_zeroₓ]⟩
  smul_mem' := fun a x ⟨b, h⟩ =>
    ⟨b, by
      rw [smul_comm, h, smul_zero]⟩

/-- The torsion submodule, containing all elements `x` of `M` such that  `a • x = 0` for some
  non-zero-divisor `a` in `R`. -/
@[reducible]
def torsion :=
  torsion' R M R⁰

end Submodule

namespace Module

/-- A `a`-torsion module is a module where every element is `a`-torsion. -/
@[reducible]
def IsTorsionBy (a : R) :=
  ∀ ⦃x : M⦄, a • x = 0

/-- A module where every element is `a`-torsion for all `a` in `s`. -/
@[reducible]
def IsTorsionBySet (s : Set R) :=
  ∀ ⦃x : M⦄ ⦃a : s⦄, (a : R) • x = 0

/-- A `S`-torsion module is a module where every element is `a`-torsion for some `a` in `S`. -/
@[reducible]
def IsTorsion' (S : Type _) [HasSmul S M] :=
  ∀ ⦃x : M⦄, ∃ a : S, a • x = 0

/-- A torsion module is a module where every element is `a`-torsion for some non-zero-divisor `a`.
-/
@[reducible]
def IsTorsion :=
  ∀ ⦃x : M⦄, ∃ a : R⁰, a • x = 0

end Module

end Defs

variable {R M : Type _}

section

variable [CommSemiringₓ R] [AddCommMonoidₓ M] [Module R M] (s : Set R) (a : R)

namespace Submodule

@[simp]
theorem smul_torsion_by (x : torsionBy R M a) : a • x = 0 :=
  Subtype.ext x.Prop

@[simp]
theorem smul_coe_torsion_by (x : torsionBy R M a) : a • (x : M) = 0 :=
  x.Prop

@[simp]
theorem mem_torsion_by_iff (x : M) : x ∈ torsionBy R M a ↔ a • x = 0 :=
  Iff.rfl

@[simp]
theorem mem_torsion_by_set_iff (x : M) : x ∈ torsionBySet R M s ↔ ∀ a : s, (a : R) • x = 0 := by
  refine' ⟨fun h ⟨a, ha⟩ => mem_Inf.mp h _ (Set.mem_image_of_mem _ ha), fun h => mem_Inf.mpr _⟩
  rintro _ ⟨a, ha, rfl⟩
  exact h ⟨a, ha⟩

@[simp]
theorem torsion_by_singleton_eq : torsionBySet R M {a} = torsionBy R M a := by
  ext x
  simp only [← mem_torsion_by_set_iff, ← SetCoe.forall, ← Subtype.coe_mk, ← Set.mem_singleton_iff, ← forall_eq, ←
    mem_torsion_by_iff]

theorem torsion_by_set_le_torsion_by_set_of_subset {s t : Set R} (st : s ⊆ t) :
    torsionBySet R M t ≤ torsionBySet R M s :=
  Inf_le_Inf fun _ ⟨a, ha, h⟩ => ⟨a, st ha, h⟩

/-- Torsion by a set is torsion by the ideal generated by it. -/
theorem torsion_by_set_eq_torsion_by_span : torsionBySet R M s = torsionBySet R M (Ideal.span s) := by
  refine' le_antisymmₓ (fun x hx => _) (torsion_by_set_le_torsion_by_set_of_subset subset_span)
  rw [mem_torsion_by_set_iff] at hx⊢
  suffices Ideal.span s ≤ Ideal.torsionOf R M x by
    rintro ⟨a, ha⟩
    exact this ha
  rw [Ideal.span_le]
  exact fun a ha => hx ⟨a, ha⟩

theorem torsion_by_span_singleton_eq : torsionBySet R M (R∙a) = torsionBy R M a :=
  (torsion_by_set_eq_torsion_by_span _).symm.trans <| torsion_by_singleton_eq _

theorem torsion_by_le_torsion_by_of_dvd (a b : R) (dvd : a ∣ b) : torsionBy R M a ≤ torsionBy R M b := by
  rw [← torsion_by_span_singleton_eq, ← torsion_by_singleton_eq]
  apply torsion_by_set_le_torsion_by_set_of_subset
  rintro c (rfl : c = b)
  exact ideal.mem_span_singleton.mpr dvd

@[simp]
theorem torsion_by_one : torsionBy R M 1 = ⊥ :=
  eq_bot_iff.mpr fun _ h => by
    rw [mem_torsion_by_iff, one_smul] at h
    exact h

@[simp]
theorem torsion_by_univ : torsionBySet R M Set.Univ = ⊥ := by
  rw [eq_bot_iff, ← torsion_by_one, ← torsion_by_singleton_eq]
  exact torsion_by_set_le_torsion_by_set_of_subset fun _ _ => trivialₓ

end Submodule

open Submodule

namespace Module

@[simp]
theorem is_torsion_by_singleton_iff : IsTorsionBySet R M {a} ↔ IsTorsionBy R M a := by
  refine' ⟨fun h x => @h _ ⟨_, Set.mem_singleton _⟩, fun h x => _⟩
  rintro ⟨b, rfl : b = a⟩
  exact @h _

theorem is_torsion_by_set_iff_torsion_by_set_eq_top : IsTorsionBySet R M s ↔ Submodule.torsionBySet R M s = ⊤ :=
  ⟨fun h => eq_top_iff.mpr fun _ _ => (mem_torsion_by_set_iff _ _).mpr <| @h _, fun h x => by
    rw [← mem_torsion_by_set_iff, h]
    trivial⟩

/-- A `a`-torsion module is a module whose `a`-torsion submodule is the full space. -/
theorem is_torsion_by_iff_torsion_by_eq_top : IsTorsionBy R M a ↔ torsionBy R M a = ⊤ := by
  rw [← torsion_by_singleton_eq, ← is_torsion_by_singleton_iff, is_torsion_by_set_iff_torsion_by_set_eq_top]

theorem is_torsion_by_set_iff_is_torsion_by_span : IsTorsionBySet R M s ↔ IsTorsionBySet R M (Ideal.span s) := by
  rw [is_torsion_by_set_iff_torsion_by_set_eq_top, is_torsion_by_set_iff_torsion_by_set_eq_top,
    torsion_by_set_eq_torsion_by_span]

theorem is_torsion_by_span_singleton_iff : IsTorsionBySet R M (R∙a) ↔ IsTorsionBy R M a :=
  (is_torsion_by_set_iff_is_torsion_by_span _).symm.trans <| is_torsion_by_singleton_iff _

end Module

namespace Submodule

open Module

theorem torsion_by_set_is_torsion_by_set : IsTorsionBySet R (torsionBySet R M s) s := fun ⟨x, hx⟩ a =>
  Subtype.ext <| (mem_torsion_by_set_iff _ _).mp hx a

/-- The `a`-torsion submodule is a `a`-torsion module. -/
theorem torsion_by_is_torsion_by : IsTorsionBy R (torsionBy R M a) a := fun _ => smul_torsion_by _ _

@[simp]
theorem torsion_by_torsion_by_eq_top : torsionBy R (torsionBy R M a) a = ⊤ :=
  (is_torsion_by_iff_torsion_by_eq_top a).mp <| torsion_by_is_torsion_by a

@[simp]
theorem torsion_by_set_torsion_by_set_eq_top : torsionBySet R (torsionBySet R M s) s = ⊤ :=
  (is_torsion_by_set_iff_torsion_by_set_eq_top s).mp <| torsion_by_set_is_torsion_by_set s

variable (R M)

theorem torsion_gc :
    @GaloisConnection (Submodule R M) (Ideal R)ᵒᵈ _ _ annihilator fun I => torsionBySet R M <| I.ofDual := fun A I =>
  ⟨fun h x hx => (mem_torsion_by_set_iff _ _).mpr fun ⟨a, ha⟩ => mem_annihilator.mp (h ha) x hx, fun h a ha =>
    mem_annihilator.mpr fun x hx => (mem_torsion_by_set_iff _ _).mp (h hx) ⟨a, ha⟩⟩

variable {R M}

section Coprime

open BigOperators

variable {ι : Type _} {p : ι → Ideal R} {S : Finset ι}

variable (hp : (S : Set ι).Pairwise fun i j => p i⊔p j = ⊤)

include hp

theorem supr_torsion_by_ideal_eq_torsion_by_infi :
    (⨆ i ∈ S, torsionBySet R M <| p i) = torsionBySet R M ↑(⨅ i ∈ S, p i) := by
  cases' S.eq_empty_or_nonempty with h h
  · rw [h]
    convert supr_emptyset
    convert torsion_by_univ
    convert top_coe
    exact infi_emptyset
    
  apply le_antisymmₓ
  · apply supr_le _
    intro i
    apply supr_le _
    intro is
    apply torsion_by_set_le_torsion_by_set_of_subset
    exact (infi_le (fun i => ⨅ H : i ∈ S, p i) i).trans (infi_le _ is)
    
  · intro x hx
    rw [mem_supr_finset_iff_exists_sum]
    obtain ⟨μ, hμ⟩ :=
      (mem_supr_finset_iff_exists_sum _ _).mp
        ((Ideal.eq_top_iff_one _).mp <| (Ideal.supr_infi_eq_top_iff_pairwise h _).mpr hp)
    refine' ⟨fun i => ⟨(μ i : R) • x, _⟩, _⟩
    · rw [mem_torsion_by_set_iff] at hx⊢
      rintro ⟨a, ha⟩
      rw [smul_smul]
      suffices : a * μ i ∈ ⨅ i ∈ S, p i
      exact hx ⟨_, this⟩
      rw [mem_infi]
      intro j
      rw [mem_infi]
      intro hj
      by_cases' ij : j = i
      · rw [ij]
        exact Ideal.mul_mem_right _ _ ha
        
      · have := coe_mem (μ i)
        simp only [← mem_infi] at this
        exact Ideal.mul_mem_left _ _ (this j hj ij)
        
      
    · simp_rw [coe_mk]
      rw [← Finset.sum_smul, hμ, one_smul]
      
    

theorem sup_indep_torsion_by_ideal : S.SupIndep fun i => torsionBySet R M <| p i := fun T hT i hi hiT => by
  rw [disjoint_iff, Finset.sup_eq_supr,
    supr_torsion_by_ideal_eq_torsion_by_infi fun i hi j hj ij => hp (hT hi) (hT hj) ij]
  have := @GaloisConnection.u_inf _ _ (OrderDual.toDual _) (OrderDual.toDual _) _ _ _ _ (torsion_gc R M)
  dsimp'  at this⊢
  rw [← this, Ideal.sup_infi_eq_top, top_coe, torsion_by_univ]
  intro j hj
  apply hp hi (hT hj)
  rintro rfl
  exact hiT hj

omit hp

variable {q : ι → R} (hq : (S : Set ι).Pairwise <| (IsCoprime on q))

include hq

theorem supr_torsion_by_eq_torsion_by_prod : (⨆ i ∈ S, torsionBy R M <| q i) = torsionBy R M (∏ i in S, q i) := by
  rw [← torsion_by_span_singleton_eq, Ideal.submodule_span_eq, ← Ideal.finset_inf_span_singleton _ _ hq,
    Finset.inf_eq_infi, ← supr_torsion_by_ideal_eq_torsion_by_infi]
  · congr
    ext : 1
    congr
    ext : 1
    exact (torsion_by_span_singleton_eq _).symm
    
  · exact fun i hi j hj ij => (Ideal.sup_eq_top_iff_is_coprime _ _).mpr (hq hi hj ij)
    

theorem sup_indep_torsion_by : S.SupIndep fun i => torsionBy R M <| q i := by
  convert sup_indep_torsion_by_ideal fun i hi j hj ij => (Ideal.sup_eq_top_iff_is_coprime (q i) _).mpr <| hq hi hj ij
  ext : 1
  exact (torsion_by_span_singleton_eq _).symm

end Coprime

end Submodule

end

section NeedsGroup

variable [CommRingₓ R] [AddCommGroupₓ M] [Module R M]

namespace Submodule

open BigOperators

variable {ι : Type _} [DecidableEq ι] {S : Finset ι}

/-- If the `p i` are pairwise coprime, a `⨅ i, p i`-torsion module is the internal direct sum of
its `p i`-torsion submodules.-/
theorem torsion_by_set_is_internal {p : ι → Ideal R} (hp : (S : Set ι).Pairwise fun i j => p i⊔p j = ⊤)
    (hM : Module.IsTorsionBySet R M (⨅ i ∈ S, p i : Ideal R)) :
    DirectSum.IsInternal fun i : S => torsionBySet R M <| p i :=
  DirectSum.is_internal_submodule_of_independent_of_supr_eq_top
    (CompleteLattice.independent_iff_sup_indep.mpr <| sup_indep_torsion_by_ideal hp)
    (((supr_subtype'' ↑S) fun i => torsionBySet R M <| p i).trans <|
      (supr_torsion_by_ideal_eq_torsion_by_infi hp).trans <|
        (Module.is_torsion_by_set_iff_torsion_by_set_eq_top _).mp hM)

/-- If the `q i` are pairwise coprime, a `∏ i, q i`-torsion module is the internal direct sum of
its `q i`-torsion submodules.-/
theorem torsion_by_is_internal {q : ι → R} (hq : (S : Set ι).Pairwise <| (IsCoprime on q))
    (hM : Module.IsTorsionBy R M <| ∏ i in S, q i) : DirectSum.IsInternal fun i : S => torsionBy R M <| q i := by
  rw [← Module.is_torsion_by_span_singleton_iff, Ideal.submodule_span_eq, ← Ideal.finset_inf_span_singleton _ _ hq,
    Finset.inf_eq_infi] at hM
  convert
    torsion_by_set_is_internal (fun i hi j hj ij => (Ideal.sup_eq_top_iff_is_coprime (q i) _).mpr <| hq hi hj ij) hM
  ext : 1
  exact (torsion_by_span_singleton_eq _).symm

end Submodule

namespace Module

variable {I : Ideal R} (hM : IsTorsionBySet R M I)

include hM

/-- can't be an instance because hM can't be inferred -/
def IsTorsionBySet.hasSmul :
    HasSmul (R ⧸ I) M where smul := fun b x =>
    (Quotientₓ.liftOn' b (· • x)) fun b₁ b₂ h => by
      show b₁ • x = b₂ • x
      have : (-b₁ + b₂) • x = 0 := @hM x ⟨_, quotient_add_group.left_rel_apply.mp h⟩
      rw [add_smul, neg_smul, neg_add_eq_zero] at this
      exact this

@[simp]
theorem IsTorsionBySet.mk_smul (b : R) (x : M) :
    have := hM.has_smul
    Ideal.Quotient.mk I b • x = b • x :=
  rfl

/-- A `(R ⧸ I)`-module is a `R`-module which `is_torsion_by_set R M I`. -/
def IsTorsionBySet.module : Module (R ⧸ I) M :=
  @Function.Surjective.moduleLeft _ _ _ _ _ _ _ hM.HasSmul _ Ideal.Quotient.mk_surjective (IsTorsionBySet.mk_smul hM)

instance IsTorsionBySet.is_scalar_tower {S : Type _} [HasSmul S R] [HasSmul S M] [IsScalarTower S R M]
    [IsScalarTower S R R] :
    @IsScalarTower S (R ⧸ I) M _ (IsTorsionBySet.module hM).toHasSmul
      _ where smul_assoc := fun b d x => (Quotientₓ.induction_on' d) fun c => (smul_assoc b c x : _)

omit hM

instance : Module (R ⧸ I) (M ⧸ I • (⊤ : Submodule R M)) :=
  IsTorsionBySet.module fun x r => by
    induction x using Quotientₓ.induction_on
    refine' (Submodule.Quotient.mk_eq_zero _).mpr (Submodule.smul_mem_smul r.prop _)
    trivial

end Module

namespace Submodule

instance (I : Ideal R) : Module (R ⧸ I) (torsionBySet R M I) :=
  Module.IsTorsionBySet.module <| torsion_by_set_is_torsion_by_set I

@[simp]
theorem torsionBySet.mk_smul (I : Ideal R) (b : R) (x : torsionBySet R M I) : Ideal.Quotient.mk I b • x = b • x :=
  rfl

instance (I : Ideal R) {S : Type _} [HasSmul S R] [HasSmul S M] [IsScalarTower S R M] [IsScalarTower S R R] :
    IsScalarTower S (R ⧸ I) (torsionBySet R M I) :=
  inferInstance

/-- The `a`-torsion submodule as a `(R ⧸ R∙a)`-module. -/
instance (a : R) : Module (R ⧸ R∙a) (torsionBy R M a) :=
  Module.IsTorsionBySet.module <| (Module.is_torsion_by_span_singleton_iff a).mpr <| torsion_by_is_torsion_by a

@[simp]
theorem torsionBy.mk_smul (a b : R) (x : torsionBy R M a) : Ideal.Quotient.mk (R∙a) b • x = b • x :=
  rfl

instance (a : R) {S : Type _} [HasSmul S R] [HasSmul S M] [IsScalarTower S R M] [IsScalarTower S R R] :
    IsScalarTower S (R ⧸ R∙a) (torsionBy R M a) :=
  inferInstance

end Submodule

end NeedsGroup

namespace Submodule

section Torsion'

open Module

variable [CommSemiringₓ R] [AddCommMonoidₓ M] [Module R M]

variable (S : Type _) [CommMonoidₓ S] [DistribMulAction S M] [SmulCommClass S R M]

@[simp]
theorem mem_torsion'_iff (x : M) : x ∈ torsion' R M S ↔ ∃ a : S, a • x = 0 :=
  Iff.rfl

@[simp]
theorem mem_torsion_iff (x : M) : x ∈ torsion R M ↔ ∃ a : R⁰, a • x = 0 :=
  Iff.rfl

@[simps]
instance : HasSmul S (torsion' R M S) :=
  ⟨fun s x =>
    ⟨s • x, by
      obtain ⟨x, a, h⟩ := x
      use a
      dsimp'
      rw [smul_comm, h, smul_zero]⟩⟩

instance : DistribMulAction S (torsion' R M S) :=
  Subtype.coe_injective.DistribMulAction (torsion' R M S).Subtype.toAddMonoidHom fun (c : S) x => rfl

instance : SmulCommClass S R (torsion' R M S) :=
  ⟨fun s a x => Subtype.ext <| smul_comm _ _ _⟩

/-- A `S`-torsion module is a module whose `S`-torsion submodule is the full space. -/
theorem is_torsion'_iff_torsion'_eq_top : IsTorsion' M S ↔ torsion' R M S = ⊤ :=
  ⟨fun h => eq_top_iff.mpr fun _ _ => @h _, fun h x => by
    rw [← @mem_torsion'_iff R, h]
    trivial⟩

/-- The `S`-torsion submodule is a `S`-torsion module. -/
theorem torsion'_is_torsion' : IsTorsion' (torsion' R M S) S := fun ⟨x, ⟨a, h⟩⟩ => ⟨a, Subtype.ext h⟩

@[simp]
theorem torsion'_torsion'_eq_top : torsion' R (torsion' R M S) S = ⊤ :=
  (is_torsion'_iff_torsion'_eq_top S).mp <| torsion'_is_torsion' S

/-- The torsion submodule of the torsion submodule (viewed as a module) is the full
torsion module. -/
@[simp]
theorem torsion_torsion_eq_top : torsion R (torsion R M) = ⊤ :=
  torsion'_torsion'_eq_top R⁰

/-- The torsion submodule is always a torsion module. -/
theorem torsion_is_torsion : Module.IsTorsion R (torsion R M) :=
  torsion'_is_torsion' R⁰

end Torsion'

section Torsion

variable [CommSemiringₓ R] [AddCommMonoidₓ M] [Module R M]

open BigOperators

theorem is_torsion_by_ideal_of_finite_of_is_torsion [Module.Finite R M] (hM : Module.IsTorsion R M) :
    ∃ I : Ideal R, (I : Set R) ∩ R⁰ ≠ ∅ ∧ Module.IsTorsionBySet R M I := by
  cases' (module.finite_def.mp inferInstance : (⊤ : Submodule R M).Fg) with S h
  refine' ⟨∏ x in S, Ideal.torsionOf R M x, _, _⟩
  · rw [Set.ne_empty_iff_nonempty]
    refine' ⟨_, _, (∏ x in S, (@hM x).some : R⁰).2⟩
    rw [Subtype.val_eq_coe, Submonoid.coe_finset_prod]
    apply Ideal.prod_mem_prod
    exact fun x _ => (@hM x).some_spec
    
  · rw [Module.is_torsion_by_set_iff_torsion_by_set_eq_top, eq_top_iff, ← h, span_le]
    intro x hx
    apply torsion_by_set_le_torsion_by_set_of_subset
    · apply Ideal.le_of_dvd
      exact Finset.dvd_prod_of_mem _ hx
      
    · rw [mem_torsion_by_set_iff]
      rintro ⟨a, ha⟩
      exact ha
      
    

variable [NoZeroDivisors R] [Nontrivial R]

theorem coe_torsion_eq_annihilator_ne_bot : (torsion R M : Set M) = { x : M | (R∙x).annihilator ≠ ⊥ } := by
  ext x
  simp_rw [Submodule.ne_bot_iff, mem_annihilator, mem_span_singleton]
  exact
    ⟨fun ⟨a, hax⟩ =>
      ⟨a, fun _ ⟨b, hb⟩ => by
        rw [← hb, smul_comm, ← Submonoid.smul_def, hax, smul_zero], nonZeroDivisors.coe_ne_zero _⟩,
      fun ⟨a, hax, ha⟩ => ⟨⟨_, mem_non_zero_divisors_of_ne_zero ha⟩, hax x ⟨1, one_smul _ _⟩⟩⟩

/-- A module over a domain has `no_zero_smul_divisors` iff its torsion submodule is trivial. -/
theorem no_zero_smul_divisors_iff_torsion_eq_bot : NoZeroSmulDivisors R M ↔ torsion R M = ⊥ := by
  constructor <;> intro h
  · have : NoZeroSmulDivisors R M := h
    rw [eq_bot_iff]
    rintro x ⟨a, hax⟩
    change (a : R) • x = 0 at hax
    cases' eq_zero_or_eq_zero_of_smul_eq_zero hax with h0 h0
    · exfalso
      exact nonZeroDivisors.coe_ne_zero a h0
      
    · exact h0
      
    
  · exact
      { eq_zero_or_eq_zero_of_smul_eq_zero := fun a x hax => by
          by_cases' ha : a = 0
          · left
            exact ha
            
          · right
            rw [← mem_bot _, ← h]
            exact ⟨⟨a, mem_non_zero_divisors_of_ne_zero ha⟩, hax⟩
             }
    

end Torsion

namespace QuotientTorsion

variable [CommRingₓ R] [AddCommGroupₓ M] [Module R M]

/-- Quotienting by the torsion submodule gives a torsion-free module. -/
@[simp]
theorem torsion_eq_bot : torsion R (M ⧸ torsion R M) = ⊥ :=
  eq_bot_iff.mpr fun z =>
    (Quotientₓ.induction_on' z) fun x ⟨a, hax⟩ => by
      rw [Quotientₓ.mk'_eq_mk, ← quotient.mk_smul, quotient.mk_eq_zero] at hax
      rw [mem_bot, Quotientₓ.mk'_eq_mk, quotient.mk_eq_zero]
      cases' hax with b h
      exact ⟨b * a, (mul_smul _ _ _).trans h⟩

instance no_zero_smul_divisors [IsDomain R] : NoZeroSmulDivisors R (M ⧸ torsion R M) :=
  no_zero_smul_divisors_iff_torsion_eq_bot.mpr torsion_eq_bot

end QuotientTorsion

section PTorsion

open Module

section

variable [Monoidₓ R] [AddCommMonoidₓ M] [DistribMulAction R M]

theorem is_torsion'_powers_iff (p : R) : IsTorsion' M (Submonoid.powers p) ↔ ∀ x : M, ∃ n : ℕ, p ^ n • x = 0 :=
  ⟨fun h x =>
    let ⟨⟨a, ⟨n, rfl⟩⟩, hx⟩ := @h x
    ⟨n, hx⟩,
    fun h x =>
    let ⟨n, hn⟩ := h x
    ⟨⟨_, ⟨n, rfl⟩⟩, hn⟩⟩

/-- In a `p ^ ∞`-torsion module (that is, a module where all elements are cancelled by scalar
multiplication by some power of `p`), the smallest `n` such that `p ^ n • x = 0`.-/
def pOrder {p : R} (hM : IsTorsion' M <| Submonoid.powers p) (x : M) [∀ n : ℕ, Decidable (p ^ n • x = 0)] :=
  Nat.findₓ <| (is_torsion'_powers_iff p).mp hM x

@[simp]
theorem pow_p_order_smul {p : R} (hM : IsTorsion' M <| Submonoid.powers p) (x : M)
    [∀ n : ℕ, Decidable (p ^ n • x = 0)] : p ^ pOrder hM x • x = 0 :=
  Nat.find_specₓ <| (is_torsion'_powers_iff p).mp hM x

end

variable [CommSemiringₓ R] [AddCommMonoidₓ M] [Module R M] [∀ x : M, Decidable (x = 0)]

theorem exists_is_torsion_by {p : R} (hM : IsTorsion' M <| Submonoid.powers p) (d : ℕ) (hd : d ≠ 0) (s : Finₓ d → M)
    (hs : span R (Set.Range s) = ⊤) : ∃ j : Finₓ d, Module.IsTorsionBy R M (p ^ pOrder hM (s j)) := by
  let oj := List.argmax (fun i => p_order hM <| s i) (List.finRange d)
  have hoj : oj.is_some :=
    option.ne_none_iff_is_some.mp fun eq_none => hd <| list.fin_range_eq_nil.mp <| list.argmax_eq_none.mp eq_none
  use Option.getₓ hoj
  rw [is_torsion_by_iff_torsion_by_eq_top, eq_top_iff, ← hs, Submodule.span_le, Set.range_subset_iff]
  intro i
  change _ • _ = _
  have : p_order hM (s i) ≤ p_order hM (s <| Option.getₓ hoj) :=
    List.le_of_mem_argmax (List.mem_fin_range i) (Option.get_memₓ hoj)
  rw [← Nat.sub_add_cancelₓ this, pow_addₓ, mul_smul, pow_p_order_smul, smul_zero]

end PTorsion

end Submodule

namespace Ideal.Quotient

open Submodule

theorem torsion_by_eq_span_singleton {R : Type _} [CommRingₓ R] (a b : R) (ha : a ∈ R⁰) :
    torsionBy R (R ⧸ R∙a * b) a = R∙mk _ b := by
  ext x
  rw [mem_torsion_by_iff, mem_span_singleton]
  obtain ⟨x, rfl⟩ := mk_surjective x
  constructor <;> intro h
  · rw [← mk_eq_mk, ← quotient.mk_smul, quotient.mk_eq_zero, mem_span_singleton] at h
    obtain ⟨c, h⟩ := h
    rw [smul_eq_mul, smul_eq_mul, mul_comm, mul_assoc, mul_cancel_left_mem_non_zero_divisor ha, mul_comm] at h
    use c
    rw [← h, ← mk_eq_mk, ← quotient.mk_smul, smul_eq_mul, mk_eq_mk]
    
  · obtain ⟨c, h⟩ := h
    rw [← h, smul_comm, ← mk_eq_mk, ← quotient.mk_smul, (quotient.mk_eq_zero _).mpr <| mem_span_singleton_self _,
      smul_zero]
    

end Ideal.Quotient

namespace AddMonoidₓ

theorem is_torsion_iff_is_torsion_nat [AddCommMonoidₓ M] : AddMonoidₓ.IsTorsion M ↔ Module.IsTorsion ℕ M := by
  refine' ⟨fun h x => _, fun h x => _⟩
  · obtain ⟨n, h0, hn⟩ := (is_of_fin_add_order_iff_nsmul_eq_zero x).mp (h x)
    exact ⟨⟨n, mem_non_zero_divisors_of_ne_zero <| ne_of_gtₓ h0⟩, hn⟩
    
  · rw [is_of_fin_add_order_iff_nsmul_eq_zero]
    obtain ⟨n, hn⟩ := @h x
    refine' ⟨n, Nat.pos_of_ne_zeroₓ (nonZeroDivisors.coe_ne_zero _), hn⟩
    

theorem is_torsion_iff_is_torsion_int [AddCommGroupₓ M] : AddMonoidₓ.IsTorsion M ↔ Module.IsTorsion ℤ M := by
  refine' ⟨fun h x => _, fun h x => _⟩
  · obtain ⟨n, h0, hn⟩ := (is_of_fin_add_order_iff_nsmul_eq_zero x).mp (h x)
    exact ⟨⟨n, mem_non_zero_divisors_of_ne_zero <| ne_of_gtₓ <| int.coe_nat_pos.mpr h0⟩, (coe_nat_zsmul _ _).trans hn⟩
    
  · rw [is_of_fin_add_order_iff_nsmul_eq_zero]
    obtain ⟨n, hn⟩ := @h x
    exact exists_nsmul_eq_zero_of_zsmul_eq_zero (nonZeroDivisors.coe_ne_zero n) hn
    

end AddMonoidₓ
