/-
Copyright (c) 2026 Yaël Dillies, Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Matteo Cipollina
-/
module

public import Mathlib.Topology.UniformSpace.UniformConvergence

/-!
# Reindexing uniform convergence
-/

@[expose] public section

open Filter

variable {ι κ α β : Type*} [UniformSpace β] {F : ι → α → β} {f : α → β} {p : Filter ι}

/-- Reindexing the domain of a uniformly convergent net. -/
theorem TendstoUniformlyOnFilter.comp_tendsto {p' : Filter α} {q : Filter κ} {u : κ → ι}
    (h : TendstoUniformlyOnFilter F f p p') (hu : Tendsto u q p) :
    TendstoUniformlyOnFilter (F ∘ u) f q p' :=
  h.mono_left hu

/-- Reindexing the domain of a net which converges uniformly on a set. -/
theorem TendstoUniformlyOn.comp_tendsto {s : Set α} {q : Filter κ} {u : κ → ι}
    (h : TendstoUniformlyOn F f p s) (hu : Tendsto u q p) :
    TendstoUniformlyOn (F ∘ u) f q s :=
  tendstoUniformlyOn_iff_tendstoUniformlyOnFilter.2 <| h.tendstoUniformlyOnFilter.comp_tendsto hu

/-- Reindexing the domain of a uniformly convergent net. -/
theorem TendstoUniformly.comp_tendsto {q : Filter κ} {u : κ → ι}
    (h : TendstoUniformly F f p) (hu : Tendsto u q p) :
    TendstoUniformly (F ∘ u) f q :=
  tendstoUniformly_iff_tendstoUniformlyOnFilter.2 <| h.tendstoUniformlyOnFilter.comp_tendsto hu

/-- A net of functions which is eventually constantly equal to `f` converges uniformly to `f`. -/
theorem tendstoUniformly_of_eventually_eq (h : ∀ᶠ n in p, F n = f) :
    TendstoUniformly F f p :=
  fun u hu ↦ h.mono fun _ hn x ↦ mem_uniformity_of_eq hu (congrFun hn x).symm
