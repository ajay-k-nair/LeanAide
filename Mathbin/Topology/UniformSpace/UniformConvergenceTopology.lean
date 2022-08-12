/-
Copyright (c) 2022 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker
-/
import Mathbin.Topology.UniformSpace.UniformConvergence
import Mathbin.Topology.UniformSpace.Pi

/-!
# Topology and uniform structure of uniform convergence

This files endows `α → β` with the topologies / uniform structures of
- uniform convergence on `α` (in the `uniform_convergence` namespace)
- uniform convergence on a specified family `𝔖` of sets of `α`
  (in the `uniform_convergence_on` namespace), also called `𝔖`-convergence

Usual examples of the second construction include :
- the topology of compact convergence, when `𝔖` is the set of compacts of `α`
- the strong topology on the dual of a TVS `E`, when `𝔖` is the set of Von Neuman bounded subsets
  of `E`
- the weak-* topology on the dual of a TVS `E`, when `𝔖` is the set of singletons of `E`.

## Main definitions

* `uniform_convergence.gen` : basis sets for the uniformity of uniform convergence
* `uniform_convergence.uniform_space` : uniform structure of uniform convergence
* `uniform_convergence_on.uniform_space` : uniform structure of 𝔖-convergence

## Main statements

* `uniform_convergence.uniform_continuous_eval` : evaluation is uniformly continuous
* `uniform_convergence.t2_space` : the topology of uniform convergence on `α → β` is T2 if
  `β` is T2.
* `uniform_convergence.tendsto_iff_tendsto_uniformly` : `uniform_convergence.uniform_space` is
  indeed the uniform structure of uniform convergence

* `uniform_convergence_on.uniform_continuous_eval_of_mem` : evaluation at a point contained in a
  set of `𝔖` is uniformly continuous
* `uniform_convergence.t2_space` : the topology of `𝔖`-convergence on `α → β` is T2 if
  `β` is T2 and `𝔖` covers `α`
* `uniform_convergence_on.tendsto_iff_tendsto_uniformly_on` :
  `uniform_convergence_on.uniform_space` is indeed the uniform structure of `𝔖`-convergence

## Implementation details

We do not declare these structures as instances, since they would conflict with `Pi.uniform_space`.

## TODO

* Show that the uniform structure of `𝔖`-convergence is exactly the structure of `𝔖'`-convergence,
  where `𝔖'` is the bornology generated by `𝔖`.
* Add a type synonym for `α → β` endowed with the structures of uniform convergence

## References

* [N. Bourbaki, *General Topology*][bourbaki1966]

## Tags

uniform convergence
-/


noncomputable section

open TopologicalSpace Classical uniformity Filter

attribute [-instance] Pi.uniformSpace

open Set Filter

namespace UniformConvergence

variable (α β : Type _) {γ ι : Type _}

variable {F : ι → α → β} {f : α → β} {s s' : Set α} {x : α} {p : Filter ι} {g : ι → α}

/-- Basis sets for the uniformity of uniform convergence -/
protected def Gen (V : Set (β × β)) : Set ((α → β) × (α → β)) :=
  { uv : (α → β) × (α → β) | ∀ x, (uv.1 x, uv.2 x) ∈ V }

variable [UniformSpace β]

protected theorem is_basis_gen : IsBasis (fun V : Set (β × β) => V ∈ 𝓤 β) (UniformConvergence.Gen α β) :=
  ⟨⟨Univ, univ_mem⟩, fun U V hU hV =>
    ⟨U ∩ V, inter_mem hU hV, fun uv huv => ⟨fun x => (huv x).left, fun x => (huv x).right⟩⟩⟩

/-- Filter basis for the uniformity of uniform convergence -/
protected def uniformityBasis : FilterBasis ((α → β) × (α → β)) :=
  (UniformConvergence.is_basis_gen α β).FilterBasis

/-- Core of the uniform structure of uniform convergence -/
protected def uniformCore : UniformSpace.Core (α → β) :=
  UniformSpace.Core.mkOfBasis (UniformConvergence.uniformityBasis α β)
    (fun U ⟨V, hV, hVU⟩ f => hVU ▸ fun x => refl_mem_uniformity hV)
    (fun U ⟨V, hV, hVU⟩ =>
      hVU ▸
        ⟨UniformConvergence.Gen α β (Prod.swap ⁻¹' V), ⟨Prod.swap ⁻¹' V, tendsto_swap_uniformity hV, rfl⟩,
          fun uv huv x => huv x⟩)
    fun U ⟨V, hV, hVU⟩ =>
    hVU ▸
      let ⟨W, hW, hWV⟩ := comp_mem_uniformity_sets hV
      ⟨UniformConvergence.Gen α β W, ⟨W, hW, rfl⟩, fun uv ⟨w, huw, hwv⟩ x => hWV ⟨w x, ⟨huw x, hwv x⟩⟩⟩

/-- Uniform structure of uniform convergence -/
protected def uniformSpace : UniformSpace (α → β) :=
  UniformSpace.ofCore (UniformConvergence.uniformCore α β)

protected theorem has_basis_uniformity :
    (@uniformity (α → β) (UniformConvergence.uniformSpace α β)).HasBasis (fun V => V ∈ 𝓤 β)
      (UniformConvergence.Gen α β) :=
  (UniformConvergence.is_basis_gen α β).HasBasis

/-- Topology of uniform convergence -/
protected def topologicalSpace : TopologicalSpace (α → β) :=
  (UniformConvergence.uniformSpace α β).toTopologicalSpace

protected theorem has_basis_nhds :
    (@nhds (α → β) (UniformConvergence.topologicalSpace α β) f).HasBasis (fun V => V ∈ 𝓤 β) fun V =>
      { g | (g, f) ∈ UniformConvergence.Gen α β V } :=
  by
  let this : UniformSpace (α → β) := UniformConvergence.uniformSpace α β
  exact nhds_basis_uniformity (UniformConvergence.has_basis_uniformity α β)

variable {α}

theorem uniform_continuous_eval (x : α) :
    @UniformContinuous _ _ (UniformConvergence.uniformSpace α β) _ (Function.eval x) := by
  change _ ≤ _
  rw [map_le_iff_le_comap, (UniformConvergence.has_basis_uniformity α β).le_basis_iff ((𝓤 _).basis_sets.comap _)]
  exact fun U hU => ⟨U, hU, fun uv huv => huv x⟩

variable {β}

theorem t2_space [T2Space β] : @T2Space _ (UniformConvergence.topologicalSpace α β) :=
  { t2 := by
      let this : UniformSpace (α → β) := UniformConvergence.uniformSpace α β
      let this : TopologicalSpace (α → β) := UniformConvergence.topologicalSpace α β
      intro f g h
      obtain ⟨x, hx⟩ := not_forall.mp (mt funext h)
      exact separated_by_continuous (uniform_continuous_eval β x).Continuous hx }

protected theorem le_Pi : UniformConvergence.uniformSpace α β ≤ Pi.uniformSpace fun _ => β := by
  rw [le_iff_uniform_continuous_id, uniform_continuous_pi]
  intro x
  exact uniform_continuous_eval β x

protected theorem tendsto_iff_tendsto_uniformly :
    Tendsto F p (@nhds _ (UniformConvergence.topologicalSpace α β) f) ↔ TendstoUniformly F f p := by
  let this : UniformSpace (α → β) := UniformConvergence.uniformSpace α β
  rw [(UniformConvergence.has_basis_nhds α β).tendsto_right_iff, TendstoUniformly]
  constructor <;>
    · intro h U hU
      filter_upwards [h (Prod.swap ⁻¹' U) (tendsto_swap_uniformity hU)]
      exact fun n => id
      

variable {α}

end UniformConvergence

namespace UniformConvergenceOn

variable (α β : Type _) {γ ι : Type _} [UniformSpace β] (𝔖 : Set (Set α))

variable {F : ι → α → β} {f : α → β} {s s' : Set α} {x : α} {p : Filter ι} {g : ι → α}

/-- Uniform structure of uniform convergence on the sets of `𝔖`. -/
protected def uniformSpace : UniformSpace (α → β) :=
  ⨅ (s : Set α) (hs : s ∈ 𝔖), UniformSpace.comap (fun f => s.restrict f) (UniformConvergence.uniformSpace s β)

/-- Topology of uniform convergence on the sets of `𝔖`. -/
protected def topologicalSpace : TopologicalSpace (α → β) :=
  (UniformConvergenceOn.uniformSpace α β 𝔖).toTopologicalSpace

protected theorem topological_space_eq :
    UniformConvergenceOn.topologicalSpace α β 𝔖 =
      ⨅ (s : Set α) (hs : s ∈ 𝔖),
        TopologicalSpace.induced (fun f => s.restrict f) (UniformConvergence.topologicalSpace s β) :=
  by
  simp only [← UniformConvergenceOn.topologicalSpace, ← to_topological_space_infi, ← to_topological_space_infi, ←
    to_topological_space_comap]
  rfl

protected theorem uniform_continuous_restrict (h : s ∈ 𝔖) :
    @UniformContinuous _ _ (UniformConvergenceOn.uniformSpace α β 𝔖) (UniformConvergence.uniformSpace s β) s.restrict :=
  by
  change _ ≤ _
  rw [UniformConvergenceOn.uniformSpace, map_le_iff_le_comap, uniformity, infi_uniformity]
  refine' infi_le_of_le s _
  rw [infi_uniformity]
  exact infi_le _ h

protected theorem uniform_space_antitone : Antitone (UniformConvergenceOn.uniformSpace α β) := fun 𝔖₁ 𝔖₂ h₁₂ =>
  infi_le_infi_of_subset h₁₂

variable {α}

theorem uniform_continuous_eval_of_mem {x : α} (hxs : x ∈ s) (hs : s ∈ 𝔖) :
    @UniformContinuous _ _ (UniformConvergenceOn.uniformSpace α β 𝔖) _ (Function.eval x) := by
  change _ ≤ _
  rw [map_le_iff_le_comap, ((𝓤 _).basis_sets.comap _).ge_iff, UniformConvergenceOn.uniformSpace, infi_uniformity']
  intro U hU
  refine' mem_infi_of_mem s _
  rw [infi_uniformity']
  exact
    mem_infi_of_mem hs
      (mem_comap.mpr
        ⟨UniformConvergence.Gen s β U, (UniformConvergence.has_basis_uniformity s β).mem_of_mem hU, fun uv huv =>
          huv ⟨x, hxs⟩⟩)

variable {β}

theorem t2_space_of_covering [T2Space β] (h : ⋃₀𝔖 = univ) : @T2Space _ (UniformConvergenceOn.topologicalSpace α β 𝔖) :=
  { t2 := by
      let this : UniformSpace (α → β) := UniformConvergenceOn.uniformSpace α β 𝔖
      let this : TopologicalSpace (α → β) := UniformConvergenceOn.topologicalSpace α β 𝔖
      intro f g hfg
      obtain ⟨x, hx⟩ := not_forall.mp (mt funext hfg)
      obtain ⟨s, hs, hxs⟩ : ∃ s ∈ 𝔖, x ∈ s := mem_sUnion.mp (h.symm ▸ True.intro)
      exact separated_by_continuous (uniform_continuous_eval_of_mem β 𝔖 hxs hs).Continuous hx }

protected theorem le_Pi_of_covering (h : ⋃₀𝔖 = univ) :
    UniformConvergenceOn.uniformSpace α β 𝔖 ≤ Pi.uniformSpace fun _ => β := by
  rw [le_iff_uniform_continuous_id, uniform_continuous_pi]
  intro x
  obtain ⟨s, hs, hxs⟩ : ∃ s ∈ 𝔖, x ∈ s := mem_sUnion.mp (h.symm ▸ True.intro)
  exact uniform_continuous_eval_of_mem β 𝔖 hxs hs

protected theorem tendsto_iff_tendsto_uniformly_on :
    Tendsto F p (@nhds _ (UniformConvergenceOn.topologicalSpace α β 𝔖) f) ↔ ∀, ∀ s ∈ 𝔖, ∀, TendstoUniformlyOn F f p s :=
  by
  let this : UniformSpace (α → β) := UniformConvergenceOn.uniformSpace α β 𝔖
  rw [UniformConvergenceOn.topological_space_eq, nhds_infi, tendsto_infi]
  refine' forall_congrₓ fun s => _
  rw [nhds_infi, tendsto_infi]
  refine' forall_congrₓ fun hs => _
  rw [nhds_induced, tendsto_comap_iff, tendsto_uniformly_on_iff_tendsto_uniformly_comp_coe,
    UniformConvergence.tendsto_iff_tendsto_uniformly]
  rfl

end UniformConvergenceOn

